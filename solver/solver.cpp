#include "solver.h"
#include "graph.h"
#include "var_flaw.h"
#include "atom_flaw.h"
#include "disjunction_flaw.h"
#include "composite_flaw.h"
#include "smart_type.h"
#include "state_variable.h"
#include "reusable_resource.h"
#include "propositional_state.h"
#include "propositional_agent.h"
#include "atom.h"
#include "combinations.h"
#ifdef BUILD_GUI
#include "solver_listener.h"
#endif
#include <algorithm>
#include <cassert>

using namespace smt;

namespace ratio
{

solver::solver() : core(), theory(get_sat_core()) {}
solver::~solver() {}

void solver::init()
{
    read(std::vector<std::string>({"init.rddl"}));
    new_types({new state_variable(*this),
               new reusable_resource(*this),
               new propositional_state(*this),
               new propositional_agent(*this)});
}

void solver::solve()
{
    build_graph(); // we build the causal graph..

    while (true)
    {
        // we solve all the inconsistencies..
        solve_inconsistencies();

        // this is the next flaw to be solved..
        flaw *f_next = select_flaw();

        if (f_next)
        {
#ifndef GRAPH_PRUNING
            if (f_next->get_estimated_cost().is_infinite()) // we don't know how to solve the next flaw: we search..
            {
                next();
                continue;
            }
#endif
            LOG("(" << std::to_string(trail.size()) << "): " << f_next->get_label());
            FIRE_CURRENT_FLAW(*f_next);

            // this is the next resolver to be assumed..
            res = f_next->get_best_resolver();
            LOG(res->get_label());
            FIRE_CURRENT_RESOLVER(*res);

            take_decision(res->rho);
            res = nullptr;
#ifdef GRAPH_PRUNING
            check_graph(); // we check whether the planning graph can be used for the search..
#endif
        }
        else
            return; // Hurray!! we have found a solution..
    }
}

void solver::build_graph()
{
    assert(get_sat_core().root_level());
    LOG("building the causal graph..");

    while (std::any_of(flaws.begin(), flaws.end(), [&](flaw *f) { return f->get_estimated_cost().is_positive_infinite(); }))
    {
        if (flaw_q.empty())
            throw std::runtime_error("the problem is unsolvable");
#ifdef DEFERRABLE_FLAWS
        assert(!flaw_q.front()->expanded);
        if (get_sat_core().value(flaw_q.front()->phi) != False)
            if (is_deferrable(*flaw_q.front())) // we have a deferrable flaw: we can postpone its expansion..
                flaw_q.push_back(flaw_q.front());
            else
                expand_flaw(*flaw_q.front()); // we expand the flaw..
        flaw_q.pop_front();
#else
        for (const auto &f : std::move(flaw_q))
            expand_flaw(*f); // we expand the flaw..
#endif
    }

    // we create and set a new graph var..
    set_new_gamma();
}

void solver::solve_inconsistencies()
{
    LOG("checking for inconsistencies..");
    std::vector<flaw *> incs;
    std::queue<type *> q;
    for (const auto &t : get_types())
        if (!t.second->is_primitive())
            q.push(t.second);

    while (!q.empty())
    {
        if (smart_type *st = dynamic_cast<smart_type *>(q.front()))
            // we collect new flaws from the smart-types and try to solve the existing ones..
            st->get_flaws(incs);
        for (const auto &st : q.front()->get_types())
            q.push(st.second);
        q.pop();
    }

    LOG("found " << std::to_string(incs.size()) << " new inconsistencies..");
    pending_flaws.insert(pending_flaws.end(), incs.begin(), incs.end());
}

void solver::expand_flaw(flaw &f)
{
    assert(!f.expanded);

    // we expand the flaw..
    if (composite_flaw *sf = dynamic_cast<composite_flaw *>(&f))
        // we expand the unexpanded enclosing flaws..
        for (const auto &c_f : sf->flaws)
            if (!c_f->expanded)
            {
                assert(!c_f->expanded);
                FIRE_CURRENT_FLAW(*c_f);
                // we expand the enclosing flaw..
                c_f->expand();
                // ..and remove it from the flaw queue..
                auto f_it = std::find(flaw_q.begin(), flaw_q.end(), c_f);
                if (f_it != flaw_q.end())
                    flaw_q.erase(f_it);

                // we apply the enclosing flaw's resolvers..
                for (const auto &r : c_f->resolvers)
                    apply_resolver(*r);
            }
    f.expand();

    for (const auto &r : f.resolvers)
        apply_resolver(*r);

    if (!get_sat_core().check())
        throw std::runtime_error("the problem is unsolvable");
}

void solver::apply_resolver(resolver &r)
{
    res = &r;
    set_ni(r.rho);
    try
    {
        r.apply();
    }
    catch (const std::runtime_error &)
    {
        if (!get_sat_core().new_clause({lit(r.rho, false)}))
            throw std::runtime_error("the problem is unsolvable");
    }

    restore_ni();
    res = nullptr;
    if (r.preconditions.empty() && get_sat_core().value(r.rho) != False) // there are no requirements for this resolver..
        set_estimated_cost(r, 0);
}

void solver::add_layer()
{
    assert(get_sat_core().root_level());
    LOG("adding a layer to the causal graph..");

    std::deque<flaw *> f_q(flaw_q);
    while (std::all_of(f_q.begin(), f_q.end(), [&](flaw *f) { return f->get_estimated_cost().is_infinite(); }))
    {
        if (flaw_q.empty())
            throw std::runtime_error("the problem is unsolvable");
        std::deque<flaw *> c_q = std::move(flaw_q);
        for (const auto &f : c_q)
            if (get_sat_core().value(f->phi) != False) // we expand the flaw..
                expand_flaw(*f);
    }

    // we create and set a new graph var..
    set_new_gamma();
}

void solver::increase_accuracy()
{
    assert(get_sat_core().root_level());
    accuracy++;
    LOG("current heuristic accuracy: " + std::to_string(accuracy));

    // we clean up composite flaws trivial flaws and already solved flaws..
    for (auto it = flaws.begin(); it != flaws.end();)
        if (composite_flaw *sf = dynamic_cast<composite_flaw *>(*it))
            // we remove the composite flaw from the current flaws..
            flaws.erase(it++);
        else if (std::any_of((*it)->resolvers.begin(), (*it)->resolvers.end(), [&](resolver *r) { return get_sat_core().value(r->rho) == True; }))
        {
            // we have either a trivial (i.e. has only one resolver) or an already solved flaw..
            assert(get_sat_core().value((*std::find_if((*it)->resolvers.begin(), (*it)->resolvers.end(), [&](resolver *r) { return get_sat_core().value(r->rho) != False; }))->rho) == True);
            // we remove the flaw from the current flaws..
            flaws.erase(it++);
        }
        else
            ++it;

    flaw_q.clear();
    if (flaws.size() >= accuracy)
    {
        std::vector<std::vector<flaw *>> fss = combinations(std::vector<flaw *>(flaws.begin(), flaws.end()), accuracy);
        for (const auto &fs : fss) // we create a new composite flaw..
            new_flaw(*new composite_flaw(*this, res, fs));
    }
    else // we create a new composite flaw..
        new_flaw(*new composite_flaw(*this, res, std::vector<flaw *>(flaws.begin(), flaws.end())));

    // we restart the building graph procedure..
    build_graph();
}

#ifdef DEFERRABLE_FLAWS
bool solver::is_deferrable(flaw &f)
{
    std::queue<flaw *> q;
    q.push(&f);
    while (!q.empty())
    {
        assert(get_sat_core().value(q.front()->phi) != False);
        if (q.front()->get_estimated_cost() < rational::POSITIVE_INFINITY) // we already have a possible solution for this flaw, thus we defer..
            return true;
        for (const auto &r : q.front()->causes)
            q.push(&r->effect);
        q.pop();
    }
    // we have an undeferrable flaw..
    return false;
}
#endif

#ifdef GRAPH_PRUNING
void solver::check_graph()
{
    // we go back at root level..
    while (!get_sat_core().root_level())
        get_sat_core().pop();
    for (const auto &f : pending_flaws)
    {
        new_flaw(*f);
        expand_flaw(*f);
    }
    pending_flaws.clear();
    while (get_sat_core().root_level())
        if (get_sat_core().value(gamma) == Undefined) // we have learnt a unit clause! thus, we reassume the graph var..
            take_decision(gamma);
        else
        {
            assert(get_sat_core().value(gamma) == False);
            // we have exhausted the search within the graph: we extend the graph..
            if (accuracy < max_accuracy)
                increase_accuracy();
            else
                add_layer();
        }
}
#endif

expr solver::new_enum(const type &tp, const std::unordered_set<item *> &allowed_vals)
{
    assert(allowed_vals.size() > 1);
    assert(tp.get_name().compare(BOOL_KEYWORD) != 0);
    assert(tp.get_name().compare(INT_KEYWORD) != 0);
    assert(tp.get_name().compare(REAL_KEYWORD) != 0);
    // we create a new enum expression..
    // notice that we do not enforce the exct_one constraint!
    var_expr xp = new var_item(*this, tp, get_ov_theory().new_var(std::unordered_set<var_value *>(allowed_vals.begin(), allowed_vals.end()), false));
    if (allowed_vals.size() > 1) // we create a new var flaw..
        new_flaw(*new var_flaw(*this, res, *xp));
    return xp;
}

void solver::new_fact(atom &atm)
{
    // we create a new atom flaw representing a fact..
    atom_flaw *af = new atom_flaw(*this, res, atm, true);
    new_flaw(*af);

    // we associate the flaw to the atom..
    reason.emplace(&atm, af);

    // we check if we need to notify the new fact to any smart types..
    if (&atm.get_type().get_scope() != this)
    {
        std::queue<type *> q;
        q.push(static_cast<type *>(&atm.get_type().get_scope()));
        while (!q.empty())
        {
            if (smart_type *st = dynamic_cast<smart_type *>(q.front()))
                st->new_fact(*af);
            for (const auto &st : q.front()->get_supertypes())
                q.push(st);
            q.pop();
        }
    }
}

void solver::new_goal(atom &atm)
{
    // we create a new atom flaw representing a goal..
    atom_flaw *af = new atom_flaw(*this, res, atm, false);
    new_flaw(*af);

    // we associate the flaw to the atom..
    reason.emplace(&atm, af);

    // we check if we need to notify the new goal to any smart types..
    if (&atm.get_type().get_scope() != this)
    {
        std::queue<type *> q;
        q.push(static_cast<type *>(&atm.get_type().get_scope()));
        while (!q.empty())
        {
            if (smart_type *st = dynamic_cast<smart_type *>(q.front()))
                st->new_goal(*af);
            for (const auto &st : q.front()->get_supertypes())
                q.push(st);
            q.pop();
        }
    }
}

void solver::new_disjunction(context &d_ctx, const disjunction &disj)
{
    // we create a new disjunction flaw..
    disjunction_flaw *df = new disjunction_flaw(*this, res, d_ctx, disj);
    new_flaw(*df);
}

bool solver::propagate(const lit &p, std::vector<lit> &cnfl)
{
    assert(cnfl.empty());
    if (!checking)
    {
        const auto at_phis_p = phis.find(p.get_var());
        if (at_phis_p != phis.end()) // a decision has been taken about the presence of some flaws within the current partial solution..
            for (const auto &f : at_phis_p->second)
            {
                FIRE_FLAW_STATE_CHANGED(*f);
                if (p.get_sign()) // this flaw has been added to the current partial solution..
                {
                    flaws.insert(f);
                    if (!trail.empty())
                        trail.back().new_flaws.insert(f);
                }
                else // this flaw has been removed from the current partial solution..
                    assert(flaws.find(f) == flaws.end());
            }

        const auto at_rhos_p = rhos.find(p.get_var());
        if (at_rhos_p != rhos.end() && !p.get_sign()) // a decision has been taken about the removal of some resolvers within the current partial solution..
            for (const auto &r : at_rhos_p->second)
            {
                FIRE_RESOLVER_STATE_CHANGED(*r);
                set_estimated_cost(*r, rational::POSITIVE_INFINITY);
            }
    }

    return true;
}

bool solver::check(std::vector<lit> &cnfl)
{
    assert(cnfl.empty());
    return true;
}

void solver::push() { LOG("level " << std::to_string(trail.size())); }

void solver::pop()
{
    if (!checking)
    {
        // we reintroduce the solved flaw..
        for (const auto &f : trail.back().solved_flaws)
            flaws.insert(f);

        // we erase the new flaws..
        for (const auto &f : trail.back().new_flaws)
            flaws.erase(f);

        // we restore the resolvers' estimated costs..
        for (const auto &r : trail.back().old_r_costs)
            r.first->est_cost = r.second;

        // we restore the flaws' estimated costs..
        for (const auto &f : trail.back().old_f_costs)
            f.first->est_cost = f.second;

#ifdef BUILD_GUI
        for (const auto &r : trail.back().old_r_costs)
            FIRE_RESOLVER_COST_CHANGED(*r.first);
        for (const auto &f : trail.back().old_f_costs)
            FIRE_FLAW_COST_CHANGED(*f.first);
#endif

        trail.pop_back();

        LOG("level " << std::to_string(trail.size()));
    }
}

void solver::new_flaw(flaw &f)
{
    f.init(); // flaws' initialization requires being at root-level..
    FIRE_NEW_FLAW(f);
    switch (sat.value(f.phi))
    {
    case True: // we have a top-level (a landmark) flaw..
        flaws.insert(&f);
        break;
    case Undefined: // we listen for the flaw to become active..
        phis[f.phi].push_back(&f);
        bind(f.phi);
        break;
    }

    // we enqueue the flaw..
    flaw_q.push_back(&f);
}

void solver::new_resolver(resolver &r)
{
    FIRE_NEW_RESOLVER(r);
    if (sat.value(r.rho) == Undefined) // we do not have a top-level (a landmark) resolver..
    {
        // we listen for the resolver to become active..
        rhos[r.rho].push_back(&r);
        bind(r.rho);
    }
}

void solver::new_causal_link(flaw &f, resolver &r)
{
    FIRE_CAUSAL_LINK_ADDED(f, r);
    r.preconditions.push_back(&f);
    f.supports.push_back(&r);
    bool new_clause = sat.new_clause({lit(r.rho, false), f.phi});
    assert(new_clause);
}

void solver::set_estimated_cost(resolver &r, const rational &cst)
{
    if (r.est_cost != cst)
    {
        if (!trail.empty()) // we store the current resolver's estimated cost, if not already stored, for allowing backtracking..
            trail.back().old_r_costs.try_emplace(&r, r.est_cost);

        // we update the resolver's estimated cost..
        r.est_cost = cst;
        FIRE_RESOLVER_COST_CHANGED(r);

        resolver *bst_res = r.effect.get_best_resolver();
        // this is the new cost of the resolver's effect..
        rational efct_cost = bst_res ? bst_res->get_estimated_cost() : rational::POSITIVE_INFINITY;
        if (r.effect.est_cost != efct_cost) // the cost of the resolver's effect has changed as a consequence of the resolver's cost update, hence, we propagate the update to all the supports of the resolver's effect..
        {
            if (!trail.empty()) // we store the current resolver's effect's estimated cost, if not already stored, for allowing backtracking..
                trail.back().old_f_costs.try_emplace(&r.effect, r.effect.est_cost);

            // we update the resolver's effect's estimated cost..
            r.effect.est_cost = efct_cost;
            FIRE_FLAW_COST_CHANGED(r.effect);

            // the resolver costs queue (for resolver cost propagation)..
            std::queue<resolver *> resolver_q;
            for (const auto &c_r : r.effect.supports)
                resolver_q.push(c_r);

            while (!resolver_q.empty())
            {
                resolver &c_res = *resolver_q.front(); // the current resolver whose cost might require an update..
                rational r_cost = evaluate(c_res.preconditions);
                if (c_res.est_cost != r_cost)
                {
                    if (!trail.empty()) // we store the current resolver's estimated cost, if not already stored, for allowing backtracking..
                        trail.back().old_r_costs.try_emplace(&c_res, c_res.est_cost);

                    // we update the resolver's estimated cost..
                    c_res.est_cost = r_cost;
                    FIRE_RESOLVER_COST_CHANGED(c_res);

                    bst_res = c_res.effect.get_best_resolver();
                    // this is the new cost of the resolver's effect..
                    efct_cost = bst_res ? bst_res->get_estimated_cost() : rational::POSITIVE_INFINITY;

                    if (c_res.effect.est_cost != efct_cost) // the cost of the resolver's effect has changed as a consequence of the resolver's cost update..
                    {
                        if (!trail.empty()) // we store the current resolver's effect's estimated cost, if not already stored, for allowing backtracking..
                            trail.back().old_f_costs.try_emplace(&c_res.effect, c_res.effect.est_cost);

                        // we update the resolver's effect's estimated cost..
                        c_res.effect.est_cost = efct_cost;
                        FIRE_FLAW_COST_CHANGED(c_res.effect);

                        for (const auto &sup_r : c_res.effect.supports) // we propagate the update to all the supports of the resolver's effect..
                            resolver_q.push(sup_r);
                    }
                }
                resolver_q.pop();
            }
        }
    }
}

const smt::rational solver::evaluate(const std::vector<flaw *> &fs)
{
    rational c_cost;
#ifdef H_MAX
    c_cost = rational::NEGATIVE_INFINITY;
    for (const auto &f : fs)
        if (!f->expanded)
            return rational::POSITIVE_INFINITY;
        else
        {
            rational c = f->get_estimated_cost();
            if (c > c_cost)
                c_cost = c;
        }
#endif
#ifdef H_ADD
    for (const auto &f : fs)
        return rational::POSITIVE_INFINITY;
    else c_cost += f->get_estimated_cost();
#endif
    return c_cost;
}

flaw *solver::select_flaw()
{
    assert(std::all_of(flaws.begin(), flaws.end(), [&](flaw *const f) { return sat.value(f->phi) == True; }));
    // this is the next flaw to be solved (i.e., the most expensive one)..
    flaw *f_next = nullptr;
    for (auto it = flaws.begin(); it != flaws.end();)
        if (std::any_of((*it)->resolvers.begin(), (*it)->resolvers.end(), [&](resolver *r) { return sat.value(r->rho) == True; }))
        {
            // we remove the flaw from the current flaws..
            if (!trail.empty())
                trail.back().solved_flaws.insert((*it));
            flaws.erase(it++);
        }
        else
        {
            // the current flaw is not trivial nor already solved: let's see if it's better than the previous one..
            if (!f_next) // this is the first flaw we see..
                f_next = *it;
            else if (f_next->get_estimated_cost() < (*it)->get_estimated_cost()) // this flaw is actually better than the previous one..
                f_next = *it;
            ++it;
        }

    return f_next;
}

void solver::set_new_gamma()
{
    // we create a new graph var..
    gamma = get_sat_core().new_var();
#ifdef BUILD_GUI
    LOG("graph var is: γ" << std::to_string(gamma));
#endif
#ifdef GRAPH_PRUNING
    // these flaws have not been expanded, hence, cannot have a solution..
    for (const auto &f : flaw_q)
        get_sat_core().new_clause({lit(gamma, false), lit(f->phi, false)});
#endif
    // we use the new graph var to allow search within the new graph..
    take_decision(gamma);
}

void solver::take_decision(const smt::lit &ch)
{
    assert(!checking);
    LOG("taking decision " << (ch.get_sign() ? std::to_string(ch.get_var()) : "!" + std::to_string(ch.get_var())));
    // we push the given resolver into the trail..
    trail.push_back(layer(ch));
    if (res)
    { // we just solved the resolver's effect..
        assert(ch.get_sign());
        assert(res->rho == ch.get_var());
        trail.back().solved_flaws.insert(&res->effect);
        flaws.erase(&res->effect);
    }

    // we take the decision..
    if (!get_sat_core().assume(ch) || !get_sat_core().check())
        throw std::runtime_error("the problem is unsolvable");
    FIRE_STATE_CHANGED();

    if (get_sat_core().root_level())
    {
        // we initialize and expand the new flaws..
        for (const auto &f : pending_flaws)
        {
            new_flaw(*f);
            expand_flaw(*f);
        }
        pending_flaws.clear();

        switch (get_sat_core().value(gamma))
        {
        case True: // the graph is perfect!
            break;
        case False:                      // we have to change the graph:
            if (accuracy < max_accuracy) // we have room for increasing the heuristic accuracy..
                increase_accuracy();     // so we increase the heuristic accuracy..
            else
                add_layer(); // we add a layer to the current graph..
            break;
        case Undefined:           // we have learnt a unit clause..
            take_decision(gamma); // we reassume gamma..
            break;
        }
    }
}

void solver::next()
{
    if (get_sat_core().root_level())
        throw std::runtime_error("the problem is unsolvable");
    std::vector<smt::lit> no_good = get_trail();
    for (size_t i = 0; i < no_good.size(); i++)
        no_good[i] = !no_good[i];
    std::reverse(no_good.begin(), no_good.end());
    get_sat_core().pop();
    record(no_good);
}

void solver::record(const std::vector<lit> &clause)
{
    theory::record(clause);
    if (!get_sat_core().check())
        throw std::runtime_error("the problem is unsolvable");
    FIRE_STATE_CHANGED();

    // we check if we need to change the graph..
    if (get_sat_core().value(gamma) == False)
    { // we do need to change the graph..
        assert(get_sat_core().root_level());
        if (accuracy < max_accuracy) // we have room for increasing the heuristic accuracy..
            increase_accuracy();     // so we increase the heuristic accuracy..
        else
            add_layer(); // we add a layer to the current graph..
    }
}

std::vector<smt::lit> solver::get_trail() const
{
    std::vector<smt::lit> c_trail;
    c_trail.reserve(trail.size());
    for (const auto &l : trail)
        c_trail.push_back(l.decision);
    return c_trail;
}

#ifdef BUILD_GUI
void solver::fire_new_flaw(const flaw &f) const
{
    for (const auto &l : listeners)
        l->new_flaw(f);
}
void solver::fire_flaw_state_changed(const flaw &f) const
{
    for (const auto &l : listeners)
        l->flaw_state_changed(f);
}
void solver::fire_flaw_cost_changed(const flaw &f) const
{
    for (const auto &l : listeners)
        l->flaw_cost_changed(f);
}
void solver::fire_current_flaw(const flaw &f) const
{
    for (const auto &l : listeners)
        l->current_flaw(f);
}
void solver::fire_new_resolver(const resolver &r) const
{
    for (const auto &l : listeners)
        l->new_resolver(r);
}
void solver::fire_resolver_state_changed(const resolver &r) const
{
    for (const auto &l : listeners)
        l->resolver_state_changed(r);
}
void solver::fire_resolver_cost_changed(const resolver &r) const
{
    for (const auto &l : listeners)
        l->resolver_cost_changed(r);
}
void solver::fire_current_resolver(const resolver &r) const
{
    for (const auto &l : listeners)
        l->current_resolver(r);
}
void solver::fire_causal_link_added(const flaw &f, const resolver &r) const
{
    for (const auto &l : listeners)
        l->causal_link_added(f, r);
}
void solver::fire_state_changed() const
{
    for (const auto &l : listeners)
        l->state_changed();
}
#endif
} // namespace ratio
