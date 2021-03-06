#include "solver.h"
#include "atom_flaw.h"
#include "disjunction_flaw.h"
#include "var_flaw.h"
#include "atom.h"
#include "smart_type.h"
#include "state_variable.h"
#include "reusable_resource.h"
#include "propositional_agent.h"
#include "propositional_state.h"
#include "hyper_flaw.h"
#include "combinations.h"
#ifndef NDEBUG
#include "solver_listener.h"
#include <iostream>
#endif
#include <algorithm>
#include <cassert>

using namespace smt;

namespace ratio
{
solver::solver() : core(), theory(sat_cr) {}
solver::~solver() {}

void solver::init()
{
    read(std::vector<std::string>({"init.rddl"}));
    new_types({new state_variable(*this), new reusable_resource(*this), new propositional_agent(*this), new propositional_state(*this)});
}

expr solver::new_enum(const type &tp, const std::unordered_set<item *> &allowed_vals)
{
    assert(!allowed_vals.empty());
    // we create a new enum expression..
    var_expr c_e = core::new_enum(tp, allowed_vals);
    if (allowed_vals.size() > 1)
    {
        // we create a new enum flaw..
        var_flaw *ef = new var_flaw(*this, res, *c_e);
        new_flaw(*ef);
    }
    return c_e;
}

void solver::new_fact(atom &atm)
{
    // we create a new atom flaw representing a fact..
    atom_flaw *af = new atom_flaw(*this, res, atm, true);
    reason.insert({&atm, af});
    new_flaw(*af);

    if (&atm.tp.get_scope() != this)
    {
        std::queue<type *> q;
        q.push(static_cast<type *>(&atm.tp.get_scope()));
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
    reason.insert({&atm, af});
    new_flaw(*af);

    if (&atm.tp.get_scope() != this)
    {
        std::queue<type *> q;
        q.push(static_cast<type *>(&atm.tp.get_scope()));
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

void solver::solve()
{
    build_graph(); // we build the causal graph..
    check_graph(); // we check whether the planning graph can be used for the search..

    while (true)
    {
        // this is the next flaw to be solved..
        flaw *f_next = select_flaw();

        if (f_next)
        {
            assert(!f_next->get_estimated_cost().is_infinite());
#ifndef NDEBUG
            std::cout << "(" << std::to_string(trail.size()) << "): " << f_next->get_label();
            // we notify the listeners that we have selected a flaw..
            for (const auto &l : listeners)
                l->current_flaw(*f_next);
#endif
#ifdef STATISTICS
            solved_flaw(*f_next);
#endif
#ifdef CHECK_INCONSISTENCIES
            if (!f_next->structural || !has_inconsistencies()) // we run out of inconsistencies, thus, we renew them..
            {
#endif
                // this is the next resolver to be assumed..
                res = f_next->get_best_resolver();
#ifndef NDEBUG
                std::cout << " " << res->get_label() << std::endl;
                // we notify the listeners that we have selected a resolver..
                for (const auto &l : listeners)
                    l->current_resolver(*res);
#endif

                // we apply the resolver..
                if (!sat_cr.assume(res->rho) || !sat_cr.check())
                    throw unsolvable_exception();

                res = nullptr;

                check_graph(); // we check whether the planning graph can be used for the search..
#ifdef CHECK_INCONSISTENCIES
            }
#endif
        }
        else if (!has_inconsistencies()) // we run out of flaws, we check for inconsistencies one last time..
            // Hurray!! we have found a solution..
            return;
    }
}

void solver::build_graph()
{
    assert(sat_cr.root_level());
#ifndef NDEBUG
    std::cout << "building the causal graph.." << std::endl;
#endif
#ifdef STATISTICS
    auto start_building = std::chrono::steady_clock::now();
#endif

    while (std::any_of(flaws.begin(), flaws.end(), [&](flaw *f) { return f->get_estimated_cost().is_positive_infinite(); }))
    {
        if (flaw_q.empty())
            throw unsolvable_exception();
#ifdef DEFERRABLES
        assert(!flaw_q.front()->expanded);
        if (sat_cr.value(flaw_q.front()->phi) != False)
            if (is_deferrable(*flaw_q.front())) // we postpone the expansion..
                flaw_q.push_back(flaw_q.front());
            else
                expand_flaw(*flaw_q.front()); // we expand the flaw..
        flaw_q.pop_front();
#else
        std::deque<flaw *> c_q = std::move(flaw_q);
        for (const auto &f : c_q)
            expand_flaw(*f); // we expand the flaw..
#endif
    }

    // we create a new graph var..
    gamma = sat_cr.new_var();
#ifndef NDEBUG
    std::cout << "graph var is: γ" << std::to_string(gamma) << std::endl;
#endif
    // these flaws have not been expanded, hence, cannot have a solution..
    for (const auto &f : flaw_q)
        sat_cr.new_clause({lit(gamma, false), lit(f->phi, false)});
    // we use the new graph var to allow search within the current graph..
    if (!sat_cr.assume(gamma) || !sat_cr.check())
        throw unsolvable_exception();
#ifdef STATISTICS
    auto end_building = std::chrono::steady_clock::now();
    graph_building_time += end_building - start_building;
#endif
}

void solver::check_graph()
{
    while (sat_cr.root_level())
        if (sat_cr.value(gamma) == Undefined)
        {
            // we have learnt a unit clause! thus, we reassume the graph var..
            if (!sat_cr.assume(gamma) || !sat_cr.check())
                throw unsolvable_exception();
        }
        else
        {
            assert(sat_cr.value(gamma) == False);
            // we have exhausted the search within the graph: we extend the graph..
            if (accuracy < max_accuracy)
                increase_accuracy();
            else
                add_layer();
        }
}

bool solver::is_deferrable(flaw &f)
{
    std::queue<flaw *> q;
    q.push(&f);
    while (!q.empty())
    {
        assert(sat_cr.value(q.front()->phi) != False);
        if (q.front()->get_estimated_cost() < rational::POSITIVE_INFINITY) // we already have a possible solution for this flaw, thus we defer..
            return true;
        for (const auto &r : q.front()->causes)
            q.push(&r->effect);
        q.pop();
    }
    // we cannot defer this flaw..
    return false;
}

void solver::add_layer()
{
    assert(sat_cr.root_level());
#ifndef NDEBUG
    std::cout << "adding a layer to the causal graph.." << std::endl;
#endif
#ifdef STATISTICS
    auto start_building = std::chrono::steady_clock::now();
#endif

    std::deque<flaw *> f_q(flaw_q);
    while (std::all_of(f_q.begin(), f_q.end(), [&](flaw *f) { return f->get_estimated_cost().is_infinite(); }))
    {
        if (flaw_q.empty())
            throw unsolvable_exception();
        std::deque<flaw *> c_q = std::move(flaw_q);
        for (const auto &f : c_q)
            if (sat_cr.value(f->phi) != False) // we expand the flaw..
                expand_flaw(*f);
    }

    // we create a new graph var..
    gamma = sat_cr.new_var();
#ifndef NDEBUG
    std::cout << "graph var is: γ" << std::to_string(gamma) << std::endl;
#endif
    // these flaws have not been expanded, hence, cannot have a solution..
    for (const auto &f : flaw_q)
        sat_cr.new_clause({lit(gamma, false), lit(f->phi, false)});
    // we use the new graph var to allow search within the new graph..
    if (!sat_cr.assume(gamma) || !sat_cr.check())
        throw unsolvable_exception();
#ifdef STATISTICS
    auto end_building = std::chrono::steady_clock::now();
    graph_building_time += end_building - start_building;
#endif
}

void solver::increase_accuracy()
{
#ifndef NDEBUG
    std::cout << "heuristic accuracy is: " + std::to_string(accuracy + 1) << std::endl;
#endif
    accuracy++;
    assert(sat_cr.root_level());

    // we clean up super-flaws trivial flaws and already solved flaws..
    for (auto it = flaws.begin(); it != flaws.end();)
        if (hyper_flaw *sf = dynamic_cast<hyper_flaw *>(*it))
            // we remove the super-flaw from the current flaws..
            flaws.erase(it++);
        else if (std::any_of((*it)->resolvers.begin(), (*it)->resolvers.end(), [&](resolver *r) { return sat_cr.value(r->rho) == True; }))
        {
            // we have either a trivial (i.e. has only one resolver) or an already solved flaw..
            assert(sat_cr.value((*std::find_if((*it)->resolvers.begin(), (*it)->resolvers.end(), [&](resolver *r) { return sat_cr.value(r->rho) != False; }))->rho) == True);
            // we remove the flaw from the current flaws..
            flaws.erase(it++);
        }
        else
            ++it;

    flaw_q.clear();
    if (flaws.size() >= accuracy)
    {
        std::vector<std::vector<flaw *>> fss = combinations(std::vector<flaw *>(flaws.begin(), flaws.end()), accuracy);
        for (const auto &fs : fss) // we create a new super flaw..
            new_flaw(*new hyper_flaw(*this, res, fs));
    }
    else // we create a new super flaw..
        new_flaw(*new hyper_flaw(*this, res, std::vector<flaw *>(flaws.begin(), flaws.end())));

    // we restart the building graph procedure..
    build_graph();
}

bool solver::has_inconsistencies()
{
#ifndef NDEBUG
    std::cout << " (checking for inconsistencies..)";
#endif
    std::vector<flaw *> incs;
    std::queue<type *> q;
    for (const auto &t : get_types())
        if (!t.second->primitive)
            q.push(t.second);

    while (!q.empty())
    {
        if (smart_type *st = dynamic_cast<smart_type *>(q.front()))
        {
            std::vector<flaw *> c_incs = st->get_flaws();
            incs.insert(incs.end(), c_incs.begin(), c_incs.end());
        }
        for (const auto &st : q.front()->get_types())
            q.push(st.second);
        q.pop();
    }

    assert(std::none_of(incs.begin(), incs.end(), [&](flaw *f) { return f->structural; }));
    if (!incs.empty())
    {
#ifndef NDEBUG
        std::cout << ": " << std::to_string(incs.size()) << std::endl;
#endif
        // we go back to root level..
        while (!sat_cr.root_level())
            sat_cr.pop();

        // we initialize the new flaws..
        for (const auto &f : incs)
        {
            f->init();
#ifndef NDEBUG
            // we notify the listeners that a new flaw has arised..
            for (const auto &l : listeners)
                l->new_flaw(*f);
#endif
#ifdef STATISTICS
            created_flaw(*f);
#endif
            expand_flaw(*f);
        }

        // we re-assume the current graph var to allow search within the current graph..
        check_graph();
        return true;
    }
    else
    {
#ifndef NDEBUG
        std::cout << std::endl;
#endif
        return false;
    }
}

flaw *solver::select_flaw()
{
    assert(std::all_of(flaws.begin(), flaws.end(), [&](flaw *const f) { return f->expanded && sat_cr.value(f->phi) == True; }));
    // this is the next flaw to be solved (i.e., the most expensive one)..
    flaw *f_next = nullptr;
    for (auto it = flaws.begin(); it != flaws.end();)
        if (std::any_of((*it)->resolvers.begin(), (*it)->resolvers.end(), [&](resolver *r) { return sat_cr.value(r->rho) == True; }))
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
            else if (f_next->structural && !(*it)->structural) // we prefere non-structural flaws (i.e., inconsistencies) to structural ones..
                f_next = *it;
            else if (f_next->structural == (*it)->structural && f_next->get_estimated_cost() < (*it)->get_estimated_cost()) // this flaw is actually better than the previous one..
                f_next = *it;
            ++it;
        }

    return f_next;
}

void solver::expand_flaw(flaw &f)
{
#ifndef NDEBUG
    for (const auto &l : listeners)
        l->current_flaw(f);
#endif
    assert(!f.expanded);
    // we expand the flaw..
    if (hyper_flaw *sf = dynamic_cast<hyper_flaw *>(&f))
        // we expand the unexpanded enclosing flaws..
        for (const auto &c_f : sf->flaws)
            if (!c_f->expanded)
            {
#ifndef NDEBUG
                for (const auto &l : listeners)
                    l->current_flaw(*c_f);
#endif
                assert(!c_f->expanded);
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

    if (!sat_cr.check())
        throw unsolvable_exception();
}

void solver::apply_resolver(resolver &r)
{
    res = &r;
    set_var(r.rho);
    try
    {
        r.apply();
    }
    catch (const inconsistency_exception &)
    {
        if (!sat_cr.new_clause({lit(r.rho, false)}))
            throw unsolvable_exception();
    }

    restore_var();
    res = nullptr;
    if (r.preconditions.empty() && sat_cr.value(r.rho) != False) // there are no requirements for this resolver..
        set_estimated_cost(r, 0);
}

void solver::new_flaw(flaw &f)
{
    f.init(); // flaws' initialization requires being at root-level..
#ifndef NDEBUG
    // we notify the listeners that a new flaw has arised..
    for (const auto &l : listeners)
        l->new_flaw(f);
#endif
#ifdef STATISTICS
    created_flaw(f);
#endif
    flaw_q.push_back(&f);
}

void solver::new_resolver(resolver &r)
{
    r.init();
#ifndef NDEBUG
    // we notify the listeners that a new resolver has arised..
    for (const auto &l : listeners)
        l->new_resolver(r);
#endif
}

void solver::new_causal_link(flaw &f, resolver &r)
{
    r.preconditions.push_back(&f);
    f.supports.push_back(&r);
    bool new_clause = sat_cr.new_clause({lit(r.rho, false), f.phi});
    assert(new_clause);
#ifndef NDEBUG
    // we notify the listeners that a new causal link has been created..
    for (const auto &l : listeners)
        l->causal_link_added(f, r);
#endif
}

void solver::set_estimated_cost(resolver &r, const rational &cst)
{
    if (r.est_cost != cst)
    {
        if (!trail.empty())
            trail.back().old_costs.insert({&r, r.est_cost});
        // this is the current cost of the resolver's effect..
        rational f_cost = r.effect.get_estimated_cost();
        // we update the resolver's estimated cost..
        r.est_cost = cst;
#ifndef NDEBUG
        // we notify the listeners that a resolver cost has changed..
        for (const auto &l : listeners)
            l->resolver_cost_changed(r);
#endif

        if (f_cost != r.effect.get_estimated_cost()) // the cost of the resolver's effect has changed as a consequence of the resolver's cost update, hence, we propagate the update to all the supports of the resolver's effect..
        {
            // the resolver costs queue (for resolver cost propagation)..
            std::queue<resolver *> resolver_q;
            for (const auto &c_r : r.effect.supports)
                resolver_q.push(c_r);

            while (!resolver_q.empty())
            {
                resolver &c_res = *resolver_q.front(); // the current resolver whose cost might require an update..
                rational r_cost = h_add(c_res.preconditions);
                if (c_res.est_cost != r_cost)
                {
                    if (!trail.empty())
                        trail.back().old_costs.insert({&c_res, c_res.est_cost});
                    // this is the current cost of the resolver's effect..
                    f_cost = c_res.effect.get_estimated_cost();
                    // we update the resolver's estimated cost..
                    c_res.est_cost = r_cost;
#ifndef NDEBUG
                    // we notify the listeners that a resolver cost has changed..
                    for (const auto &l : listeners)
                        l->resolver_cost_changed(c_res);
#endif

                    if (f_cost != c_res.effect.get_estimated_cost())  // the cost of the resolver's effect has changed as a consequence of the resolver's cost update..
                        for (const auto &c_r : c_res.effect.supports) // hence, we propagate the update to all the supports of the resolver's effect..
                            resolver_q.push(c_r);
                }
                resolver_q.pop();
            }
        }
    }
}

const smt::rational solver::h_max(const std::vector<flaw *> &fs)
{
    rational c_cost = rational::NEGATIVE_INFINITY;
    for (const auto &f : fs)
    {
        rational c = f->get_estimated_cost();
        if (c > c_cost)
            c_cost = c;
    }
    return c_cost;
}
const smt::rational solver::h_add(const std::vector<flaw *> &fs)
{
    rational c_cost;
    for (const auto &f : fs)
        c_cost += f->get_estimated_cost();
    return c_cost;
}

bool solver::propagate(const lit &p, std::vector<lit> &cnfl)
{
    assert(cnfl.empty());
    const auto at_phis_p = phis.find(p.v);
    if (at_phis_p != phis.end()) // a decision has been taken about the presence of some flaws within the current partial solution..
        for (const auto &f : at_phis_p->second)
            if (p.sign) // this flaw has been added to the current partial solution..
            {
                flaws.insert(f);
                if (!trail.empty())
                    trail.back().new_flaws.insert(f);
#ifndef NDEBUG
                // we notify the listeners that the state of the flaw has changed..
                for (const auto &l : listeners)
                    l->flaw_state_changed(*f);
#endif
            }
            else // this flaw has been removed from the current partial solution..
                assert(flaws.find(f) == flaws.end());

    const auto at_rhos_p = rhos.find(p.v);
    if (at_rhos_p != rhos.end() && !p.sign) // a decision has been taken about the removal of some resolvers within the current partial solution..
        for (const auto &r : at_rhos_p->second)
            set_estimated_cost(*r, rational::POSITIVE_INFINITY);

    return true;
}

bool solver::check(std::vector<lit> &cnfl)
{
    assert(cnfl.empty());
    return true;
}

void solver::push()
{
    trail.push_back(layer(res));
    if (res)
    {
        // we just solved the resolver's effect..
        trail.back().solved_flaws.insert(&res->effect);
        flaws.erase(&res->effect);
    }
}

void solver::pop()
{
    // we reintroduce the solved flaw..
    for (const auto &f : trail.back().solved_flaws)
        flaws.insert(f);

    // we erase the new flaws..
    for (const auto &f : trail.back().new_flaws)
        flaws.erase(f);

    // we restore the resolvers' estimated costs..
    for (const auto &r : trail.back().old_costs)
        r.first->est_cost = r.second;

#ifndef NDEBUG
    // we notify the listeners that the cost of some resolvers has been restored..
    for (const auto &l : listeners)
        for (const auto &c : trail.back().old_costs)
            l->resolver_cost_changed(*c.first);
#endif

    trail.pop_back();
}

#ifdef STATISTICS
void solver::created_flaw(flaw &f)
{
    if (hyper_flaw *hf = dynamic_cast<hyper_flaw *>(&f))
    { // do nothing..
    }
    else if (atom_flaw *af = dynamic_cast<atom_flaw *>(&f))
        if (af->is_fact)
            n_created_facts++;
        else
            n_created_goals++;
    else if (disjunction_flaw *df = dynamic_cast<disjunction_flaw *>(&f))
        n_created_disjs++;
    else if (var_flaw *ef = dynamic_cast<var_flaw *>(&f))
        n_created_vars++;
    else
        n_created_incs++;
}

void solver::solved_flaw(flaw &f)
{
    if (hyper_flaw *hf = dynamic_cast<hyper_flaw *>(&f))
        for (const auto &c_f : hf->flaws)
            solved_flaw(*c_f);
    else if (atom_flaw *af = dynamic_cast<atom_flaw *>(&f))
        if (af->is_fact)
            n_solved_facts++;
        else
            n_solved_goals++;
    else if (disjunction_flaw *df = dynamic_cast<disjunction_flaw *>(&f))
        n_solved_disjs++;
    else if (var_flaw *ef = dynamic_cast<var_flaw *>(&f))
        n_solved_vars++;
    else
        n_solved_incs++;
}
#endif
}