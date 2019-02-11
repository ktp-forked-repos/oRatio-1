#include "reusable_resource.h"
#include "solver.h"
#include "atom.h"
#include "field.h"
#include "atom_flaw.h"
#include "combinations.h"
#include "riddle_parser.h"

using namespace smt;

namespace ratio
{

reusable_resource::reusable_resource(solver &slv) : smart_type(slv, slv, REUSABLE_RESOURCE_NAME)
{
    new_fields(*this, {new field(slv.get_type("real"), REUSABLE_RESOURCE_CAPACITY)}); // we add the 'capacity' field..
    new_constructors({new rr_constructor(*this)});                                    // we add a constructor..
    new_predicates({new use_predicate(*this)}, false);                                // we add the 'Use' predicate, without notifying neither the resource nor its supertypes..
}
reusable_resource::~reusable_resource() {}

std::vector<flaw *> reusable_resource::get_flaws()
{
    std::vector<flaw *> flaws;
    if (to_check.empty()) // nothing has changed since last inconsistency check..
        return flaws;
    else
    {
        std::vector<rr_flaw *> c_flaws;

        // we enter into the main scheduling loop..
        while (true)
        {
        sched_loop:
            c_flaws.clear();
            // we partition atoms for each reusable-resource they might insist on..
            std::unordered_map<item *, std::vector<atom *>> rr_instances;
            for (const auto &a : atoms)
                if (get_core().get_sat_core().value(a.first->get_sigma()) == True) // we filter out those atoms which are not strictly active..
                {
                    expr c_scope = a.first->get(TAU);
                    if (var_item *enum_scope = dynamic_cast<var_item *>(&*c_scope))
                    {
                        for (const auto &val : get_core().get_ov_theory().value(enum_scope->ev))
                            if (to_check.find(static_cast<item *>(val)) != to_check.end())
                                rr_instances[static_cast<item *>(val)].push_back(a.first);
                    }
                    else
                        rr_instances[static_cast<item *>(&*c_scope)].push_back(a.first);
                }

            // we detect flaws for each of the instances..
            for (const auto &rr : rr_instances)
            {
                // for each pulse, the atoms starting at that pulse..
                std::map<inf_rational, std::set<atom *>> starting_atoms;
                // for each pulse, the atoms ending at that pulse..
                std::map<inf_rational, std::set<atom *>> ending_atoms;
                // all the pulses of the timeline..
                std::set<inf_rational> pulses;
                // the resource capacity..
                arith_expr capacity = rr.first->get(REUSABLE_RESOURCE_CAPACITY);
                inf_rational c_capacity = get_core().arith_value(capacity);

                for (const auto &a : rr.second)
                {
                    arith_expr s_expr = a->get(START);
                    arith_expr e_expr = a->get(END);
                    inf_rational start = get_core().arith_value(s_expr);
                    inf_rational end = get_core().arith_value(e_expr);
                    starting_atoms[start].insert(a);
                    ending_atoms[end].insert(a);
                    pulses.insert(start);
                    pulses.insert(end);
                }

                std::set<atom *> overlapping_atoms;
                for (const auto &p : pulses)
                {
                    const auto at_start_p = starting_atoms.find(p);
                    if (at_start_p != starting_atoms.end())
                        overlapping_atoms.insert(at_start_p->second.begin(), at_start_p->second.end());
                    const auto at_end_p = ending_atoms.find(p);
                    if (at_end_p != ending_atoms.end())
                        for (const auto &a : at_end_p->second)
                            overlapping_atoms.erase(a);
                    inf_rational c_usage; // the concurrent resource usage..
                    for (const auto &a : overlapping_atoms)
                    {
                        arith_expr amount = a->get(REUSABLE_RESOURCE_USE_AMOUNT_NAME);
                        c_usage += get_core().arith_value(amount);
                    }

                    if (c_usage > c_capacity) // we have a 'peak'..
                    {
                        auto flw_it = rr_flaws.find(overlapping_atoms);
                        rr_flaw *flw;
                        if (flw_it == rr_flaws.end())
                        {
                            flw = new rr_flaw(get_solver(), overlapping_atoms);
                            c_flaws.push_back(flw);
                            flaws.push_back(flw);
                        }
                        else
                            flw = flw_it->second;
                    }
                }
            }

            to_check.clear();

            if (c_flaws.empty())
                break; // we exit from the main scheduling loop..
            else
            {
                std::vector<std::pair<lit, double>> bst_flw;
                double k_inv = std::numeric_limits<double>::infinity();
                for (const auto &flw : c_flaws)
                {
                    std::vector<std::pair<lit, double>> eval = flw->evaluate();
                    switch (eval.size())
                    {
                    case 0: // we have an unsolvable flaw: we backtrack..
                    {
                        if (get_solver().get_sat_core().root_level())
                            throw std::runtime_error("the problem is unsolvable");
                        std::vector<smt::lit> trail = get_trail();
                        std::vector<smt::lit> no_good(trail.rbegin(), trail.rend());
                        no_good[0] = !no_good[0];
                        get_solver().get_sat_core().pop();
                        record(no_good);
                        if (!get_solver().get_sat_core().check())
                            throw std::runtime_error("the problem is unsolvable");
                        goto sched_loop;
                    }
                    case 1: // we have a deterministic flaw..
                        if (!get_solver().get_sat_core().assume(eval.at(0).first) || !get_solver().get_sat_core().check())
                            throw std::runtime_error("the problem is unsolvable");
                        goto sched_loop;
                    default: // we have to take a decision..
                        double bst_commit = std::numeric_limits<double>::infinity();
                        for (const auto &evl : eval)
                            if (evl.second < bst_commit)
                                bst_commit = evl.second;
                        double c_k_inv = 0;
                        for (const auto &evl : eval)
                            c_k_inv += 1l / (1l + evl.second - bst_commit);
                        if (c_k_inv < k_inv)
                        {
                            k_inv = c_k_inv;
                            bst_flw = eval;
                        }
                        break;
                    }
                }
                lit bst_choice;
                double bst_commit = std::numeric_limits<double>::infinity();
                for (const auto &evl : bst_flw)
                    if (evl.second < bst_commit)
                    {
                        bst_choice = evl.first;
                        bst_commit = evl.second;
                    }
                if (!get_solver().get_sat_core().assume(bst_choice) || !get_solver().get_sat_core().check())
                    throw std::runtime_error("the problem is unsolvable");
            }
        }
        return flaws;
    }
}

void reusable_resource::new_fact(atom_flaw &f)
{
    // we apply interval-predicate whenever the fact becomes active..
    atom &atm = f.get_atom();
    set_ni(atm.get_sigma());
    static_cast<predicate &>(get_predicate(REUSABLE_RESOURCE_USE_PREDICATE_NAME)).apply_rule(atm);
    restore_ni();

    // we avoid unification..
    if (!get_core().get_sat_core().new_clause({lit(f.get_phi(), false), atm.get_sigma()}))
        throw std::runtime_error("the problem is unsolvable");

    for (const auto &c_atm : atoms)
    {
        expr a0_tau = atm.get(TAU);
        expr a1_tau = c_atm.first->get(TAU);
        item *a0_tau_itm = dynamic_cast<var_item *>(&*a0_tau);
        item *a1_tau_itm = dynamic_cast<var_item *>(&*a1_tau);
        if (a0_tau_itm || a1_tau_itm)
        {
            if (a0_tau_itm && a1_tau_itm)
            {
                // we have two non-singleton variables..
                std::unordered_set<var_value *> a0_vals = get_solver().enum_value(static_cast<var_item *>(a0_tau_itm));
                std::unordered_set<var_value *> a1_vals = get_solver().enum_value(static_cast<var_item *>(a1_tau_itm));

                bool found = false;
                for (const auto &v0 : a0_vals)
                    if (a1_vals.find(v0) != a1_vals.end())
                    {
                        found = true;
                        break;
                    }
                if (found)
                { // we prepare the variables..
                    arith_expr a0_start = atm.get(START);
                    arith_expr a0_end = atm.get(END);
                    arith_expr a1_start = c_atm.first->get(START);
                    arith_expr a1_end = c_atm.first->get(END);
                    get_solver().leq(a0_end, a1_start);
                    get_solver().leq(a1_end, a0_start);

                    std::unordered_set<var_value *> a0_vals = get_solver().enum_value(static_cast<var_item *>(a0_tau_itm));
                    std::unordered_set<var_value *> a1_vals = get_solver().enum_value(static_cast<var_item *>(a1_tau_itm));
                    if (a0_vals.size() == 1 || a1_vals.size() == 1)
                    {
                        a0_tau_itm->eq(*a1_tau_itm);
                        a1_tau_itm->eq(*a0_tau_itm);
                    }
                    else
                        for (const auto &v0 : a0_vals)
                            for (const auto &v1 : a1_vals)
                                if (v0 != v1)
                                    get_solver().get_sat_core().new_conj({a0_tau_itm->eq(*static_cast<item *>(v0)), a1_tau_itm->eq(*static_cast<item *>(v1))});
                }
            }
            else if (!a0_tau_itm)
            {
                std::unordered_set<var_value *> a1_vals = get_solver().enum_value(static_cast<var_item *>(a1_tau_itm));
                if (a1_vals.find(&*a0_tau) != a1_vals.end())
                { // we prepare the variables..
                    arith_expr a0_start = atm.get(START);
                    arith_expr a0_end = atm.get(END);
                    arith_expr a1_start = c_atm.first->get(START);
                    arith_expr a1_end = c_atm.first->get(END);
                    get_solver().leq(a0_end, a1_start);
                    get_solver().leq(a1_end, a0_start);
                    (&*a0_tau)->eq(*a1_tau_itm);
                    a1_tau_itm->eq(*a0_tau);
                }
            }
            else if (!a1_tau_itm)
            {
                std::unordered_set<var_value *> a0_vals = get_solver().enum_value(static_cast<var_item *>(a0_tau_itm));
                if (a0_vals.find(&*a0_tau) != a0_vals.end())
                { // we prepare the variables..
                    arith_expr a0_start = atm.get(START);
                    arith_expr a0_end = atm.get(END);
                    arith_expr a1_start = c_atm.first->get(START);
                    arith_expr a1_end = c_atm.first->get(END);
                    get_solver().leq(a0_end, a1_start);
                    get_solver().leq(a1_end, a0_start);
                    (&*a1_tau)->eq(*a0_tau_itm);
                    a0_tau_itm->eq(*a1_tau);
                }
            }
        }
        else if (&*a0_tau == &*a1_tau)
        { // the two atoms are on the same reusable resource..
            arith_expr a0_start = atm.get(START);
            arith_expr a0_end = atm.get(END);
            arith_expr a1_start = c_atm.first->get(START);
            arith_expr a1_end = c_atm.first->get(END);
            get_solver().leq(a0_end, a1_start);
            get_solver().leq(a1_end, a0_start);
        }
    }
    atoms.push_back({&atm, new rr_atom_listener(*this, atm)});

    // we filter out those atoms which are not strictly active..
    if (get_core().get_sat_core().value(atm.get_sigma()) == True)
    {
        expr c_scope = atm.get(TAU);
        if (var_item *enum_scope = dynamic_cast<var_item *>(&*c_scope))              // the 'tau' parameter is a variable..
            for (const auto &val : get_core().get_ov_theory().value(enum_scope->ev)) // we check for all its allowed values..
                to_check.insert(static_cast<item *>(val));
        else // the 'tau' parameter is a constant..
            to_check.insert(&*c_scope);
    }
}

void reusable_resource::new_goal(atom_flaw &) { throw std::logic_error("it is not possible to define goals on a reusable resource.."); }

reusable_resource::rr_constructor::rr_constructor(reusable_resource &rr) : constructor(rr.get_core(), rr, {new field(rr.get_core().get_type(REAL_KEYWORD), REUSABLE_RESOURCE_CAPACITY)}, {{REUSABLE_RESOURCE_CAPACITY, {static_cast<const ast::expression *>(new ast::id_expression({REUSABLE_RESOURCE_CAPACITY}))}}}, {static_cast<const ast::statement *>(new ast::expression_statement(static_cast<const ast::expression *>(new ast::geq_expression(static_cast<const ast::expression *>(new ast::id_expression({REUSABLE_RESOURCE_CAPACITY})), static_cast<const ast::expression *>(new ast::real_literal_expression(0))))))}) {}
reusable_resource::rr_constructor::~rr_constructor() {}

reusable_resource::use_predicate::use_predicate(reusable_resource &rr) : predicate(rr.get_core(), rr, REUSABLE_RESOURCE_USE_PREDICATE_NAME, {new field(rr.get_core().get_type(REAL_KEYWORD), REUSABLE_RESOURCE_USE_AMOUNT_NAME), new field(rr, TAU)}, {static_cast<const ast::statement *>(new ast::expression_statement(static_cast<const ast::expression *>(new ast::geq_expression(static_cast<const ast::expression *>(new ast::id_expression({REUSABLE_RESOURCE_USE_AMOUNT_NAME})), static_cast<const ast::expression *>(new ast::real_literal_expression(0))))))}) { new_supertypes({&rr.get_core().get_predicate("IntervalPredicate")}); }
reusable_resource::use_predicate::~use_predicate() {}

reusable_resource::rr_atom_listener::rr_atom_listener(reusable_resource &rr, atom &atm) : atom_listener(atm), rr(rr) {}
reusable_resource::rr_atom_listener::~rr_atom_listener() {}

void reusable_resource::rr_atom_listener::something_changed()
{
    // we filter out those atoms which are not strictly active..
    if (atm.get_core().get_sat_core().value(atm.get_sigma()) == True)
    {
        expr c_scope = atm.get(TAU);
        if (var_item *enum_scope = dynamic_cast<var_item *>(&*c_scope))                  // the 'tau' parameter is a variable..
            for (const auto &val : atm.get_core().get_ov_theory().value(enum_scope->ev)) // we check for all its allowed values..
                rr.to_check.insert(static_cast<item *>(val));
        else // the 'tau' parameter is a constant..
            rr.to_check.insert(&*c_scope);
    }
}

reusable_resource::rr_flaw::rr_flaw(solver &slv, const std::set<atom *> &atms) : flaw(slv, smart_type::get_resolvers(slv, atms)), overlapping_atoms(atms) {}
reusable_resource::rr_flaw::~rr_flaw() {}

#ifdef BUILD_GUI
std::string reusable_resource::rr_flaw::get_label() const
{
    return "φ" + std::to_string(get_phi()) + " rr-flaw";
}
#endif

std::vector<std::pair<lit, double>> reusable_resource::rr_flaw::evaluate()
{
    std::vector<std::pair<lit, double>> choices;
    std::vector<std::vector<atom *>> cs = combinations(std::vector<atom *>(overlapping_atoms.begin(), overlapping_atoms.end()), 2);
    for (const auto &as : cs)
    {
        arith_expr a0_start = as[0]->get(START);
        arith_expr a0_end = as[0]->get(END);
        arith_expr a1_start = as[1]->get(START);
        arith_expr a1_end = as[1]->get(END);

        bool_expr a0_before_a1 = slv.leq(a0_end, a1_start);
        if (slv.bool_value(a0_before_a1) != False)
        {
            rational work = (slv.arith_value(a1_end).get_rational() - slv.arith_value(a1_start).get_rational()) * (slv.arith_value(a0_end).get_rational() - slv.arith_value(a1_start).get_rational());
            choices.push_back({a0_before_a1->l, 1l - 1l / (static_cast<double>(work.numerator()) / work.denominator())});
        }
        bool_expr a1_before_a0 = slv.leq(a1_end, a0_start);
        if (slv.bool_value(a1_before_a0) != False)
        {
            rational work = (slv.arith_value(a0_end).get_rational() - slv.arith_value(a0_start).get_rational()) * (slv.arith_value(a1_end).get_rational() - slv.arith_value(a0_start).get_rational());
            choices.push_back({a1_before_a0->l, 1l - 1l / (static_cast<double>(work.numerator()) / work.denominator())});
        }

        expr a0_tau = as[0]->get(TAU);
        expr a1_tau = as[1]->get(TAU);
        item *a0_tau_itm = dynamic_cast<var_item *>(&*a0_tau);
        item *a1_tau_itm = dynamic_cast<var_item *>(&*a1_tau);
        if (a0_tau_itm || a1_tau_itm)
        {
            if (a0_tau_itm && a1_tau_itm)
            {
                // we have two non-singleton variables..
                std::unordered_set<var_value *> a0_vals = slv.enum_value(static_cast<var_item *>(a0_tau_itm));
                std::unordered_set<var_value *> a1_vals = slv.enum_value(static_cast<var_item *>(a1_tau_itm));
                size_t tot = a0_vals.size() * a1_vals.size();
                if (a0_vals.size() == 1 || a1_vals.size() == 1)
                {
                    lit choice(a0_tau_itm->eq(*a1_tau_itm), false);
                    if (slv.get_sat_core().value(choice) != False)
                        choices.push_back({choice, 1l - (static_cast<double>(tot) - 1) / static_cast<double>(tot)});
                }
                else
                    for (const auto &v0 : a0_vals)
                        for (const auto &v1 : a1_vals)
                            if (v0 != v1)
                            {
                                lit choice(slv.get_sat_core().new_conj({a0_tau_itm->eq(*static_cast<item *>(v0)), a1_tau_itm->eq(*static_cast<item *>(v1))}));
                                if (slv.get_sat_core().value(choice) != False)
                                    choices.push_back({choice, 1l - 1l / static_cast<double>(tot)});
                            }
            }
            else if (!a0_tau_itm)
            {
                size_t tot = slv.enum_value(static_cast<var_item *>(a1_tau_itm)).size();
                lit choice((&*a0_tau)->eq(*a1_tau_itm), false);
                if (slv.get_sat_core().value(choice) != False)
                    choices.push_back({choice, 1 - (static_cast<double>(tot) - 1l) / static_cast<double>(tot)});
            }
            else if (!a1_tau_itm)
            {
                size_t tot = slv.enum_value(static_cast<var_item *>(a0_tau_itm)).size();
                lit choice((&*a1_tau)->eq(*a0_tau_itm), false);
                if (slv.get_sat_core().value(choice) != False)
                    choices.push_back({choice, 1 - (static_cast<double>(tot) - 1l) / static_cast<double>(tot)});
            }
        }
    }
    return choices;
}

void reusable_resource::rr_flaw::compute_resolvers()
{
    std::vector<std::vector<atom *>> cs = combinations(std::vector<atom *>(overlapping_atoms.begin(), overlapping_atoms.end()), 2);
    for (const auto &as : cs)
    {
        arith_expr a0_start = as[0]->get(START);
        arith_expr a0_end = as[0]->get(END);
        arith_expr a1_start = as[1]->get(START);
        arith_expr a1_end = as[1]->get(END);

        bool_expr a0_before_a1 = slv.leq(a0_end, a1_start);
        if (slv.bool_value(a0_before_a1) != False)
            add_resolver(*new order_resolver(slv, a0_before_a1->l.get_var(), *this, *as[0], *as[1]));
        bool_expr a1_before_a0 = slv.leq(a1_end, a0_start);
        if (slv.bool_value(a1_before_a0) != False)
            add_resolver(*new order_resolver(slv, a1_before_a0->l.get_var(), *this, *as[1], *as[0]));

        expr a0_tau = as[0]->get(TAU);
        expr a1_tau = as[1]->get(TAU);
        item *a0_tau_itm = dynamic_cast<var_item *>(&*a0_tau);
        item *a1_tau_itm = dynamic_cast<var_item *>(&*a1_tau);
        if (a0_tau_itm || a1_tau_itm)
        {
            if (a0_tau_itm && a1_tau_itm)
            {
                // we have two non-singleton variables..
                std::unordered_set<var_value *> a0_vals = slv.enum_value(static_cast<var_item *>(a0_tau_itm));
                std::unordered_set<var_value *> a1_vals = slv.enum_value(static_cast<var_item *>(a1_tau_itm));
                size_t tot = a0_vals.size() * a1_vals.size();
                if (a0_vals.size() == 1 || a1_vals.size() == 1)
                    add_resolver(*new displace_resolver(slv, *this, *as[0], *as[1], lit(a0_tau_itm->eq(*a1_tau_itm), false)));
                else
                    for (const auto &v0 : a0_vals)
                        for (const auto &v1 : a1_vals)
                            if (v0 != v1)
                            {
                                lit choice(slv.get_sat_core().new_conj({a0_tau_itm->eq(*static_cast<item *>(v0)), a1_tau_itm->eq(*static_cast<item *>(v1))}));
                                if (slv.get_sat_core().value(choice) != False)
                                    add_resolver(*new place_resolver(slv, *this, *as[0], *as[1], choice));
                            }
            }
            else if (!a0_tau_itm)
                add_resolver(*new displace_resolver(slv, *this, *as[0], *as[1], lit(a0_tau->eq(*a1_tau_itm), false)));
            else if (!a1_tau_itm)
                add_resolver(*new displace_resolver(slv, *this, *as[0], *as[1], lit(a1_tau->eq(*a0_tau_itm), false)));
        }
    }
}

reusable_resource::order_resolver::order_resolver(solver &slv, const var &r, rr_flaw &f, const atom &before, const atom &after) : resolver(slv, r, 0, f), before(before), after(after) {}
reusable_resource::order_resolver::~order_resolver() {}

#ifdef BUILD_GUI
std::string reusable_resource::order_resolver::get_label() const
{
    return "ρ" + std::to_string(get_rho()) + " σ" + std::to_string(before.get_sigma()) + " <= σ" + std::to_string(after.get_sigma());
}
#endif

void reusable_resource::order_resolver::apply()
{
}

reusable_resource::place_resolver::place_resolver(solver &slv, rr_flaw &f, const atom &a0, const atom &a1, const lit &neq_lit) : resolver(slv, 0, f), a0(a0), a1(a1), neq_lit(neq_lit) {}
reusable_resource::place_resolver::~place_resolver() {}

#ifdef BUILD_GUI
std::string reusable_resource::place_resolver::get_label() const
{
    return "ρ" + std::to_string(get_rho()) + " pl σ" + std::to_string(a0.get_sigma()) + ".τ && σ" + std::to_string(a1.get_sigma()) + ".τ";
}
#endif

void reusable_resource::place_resolver::apply()
{
}

reusable_resource::displace_resolver::displace_resolver(solver &slv, rr_flaw &f, const atom &a0, const atom &a1, const lit &neq_lit) : resolver(slv, 0, f), a0(a0), a1(a1), neq_lit(neq_lit) {}
reusable_resource::displace_resolver::~displace_resolver() {}

#ifdef BUILD_GUI
std::string reusable_resource::displace_resolver::get_label() const
{
    return "ρ" + std::to_string(get_rho()) + " displ σ" + std::to_string(a0.get_sigma()) + ".τ != σ" + std::to_string(a1.get_sigma()) + ".τ";
}
#endif

void reusable_resource::displace_resolver::apply()
{
    slv.get_sat_core().new_clause({lit(get_rho(), false), neq_lit});
}
} // namespace ratio