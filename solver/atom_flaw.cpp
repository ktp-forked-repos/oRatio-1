#include "atom_flaw.h"
#include "solver.h"
#include "atom.h"
#include "smart_type.h"
#include "predicate.h"
#include <cassert>

using namespace smt;

namespace ratio
{

inline const std::vector<resolver *> get_cause(resolver *const cause)
{
    if (cause)
        return {cause};
    else
        return {};
}

atom_flaw::atom_flaw(solver &slv, resolver *const cause, atom &atm, const bool is_fact) : flaw(slv, get_cause(cause), true, true), atm(atm), is_fact(is_fact) {}
atom_flaw::~atom_flaw() {}

void atom_flaw::compute_resolvers()
{
    assert(slv.get_sat_core().value(get_phi()) != False);
    assert(slv.get_sat_core().value(atm.get_sigma()) != False);
    if (slv.get_sat_core().value(atm.get_sigma()) == Undefined) // we check if the atom can unify..
    {
        // we collect the ancestors of this flaw, so as to avoid cyclic causality..
        std::unordered_set<const flaw *> ancestors;
        std::queue<const flaw *> q;
        q.push(this);
        while (!q.empty())
        {
            if (ancestors.find(q.front()) == ancestors.end())
            {
                ancestors.insert(q.front());
                for (const auto &supp : q.front()->get_causes())
                    if (slv.get_sat_core().value(supp->get_rho()) != False) // if false, the edge is broken..
                        q.push(&supp->get_effect());                        // we push its effect..
            }
            q.pop();
        }

        const smart_type *tp = static_cast<const smart_type *>(&atm.get_type());
        for (const auto &i : tp->get_instances())
        {
            if (&*i == &atm) // the current atom cannot unify with itself..
                continue;

            // this is the atom we are checking for unification..
            atom &t_atm = static_cast<atom &>(*i);

            // this is the target flaw (i.e. the one we are checking for unification) and cannot be in the current flaw's causes' effects..
            atom_flaw &target = tp->get_reason(t_atm);

            if (!target.is_expanded() ||                                // the target flaw must hav been already expanded..
                ancestors.find(&target) != ancestors.end() ||           // unifying with the target atom would introduce cyclic causality..
                slv.get_sat_core().value(t_atm.get_sigma()) == False || // the target atom is unified with some other atom..
                !atm.equates(t_atm))                                    // the atom does not equate with the target target..
                continue;

            // the equality propositional variable..
            var eq_v = atm.eq(t_atm);

            if (slv.get_sat_core().value(eq_v) == False) // the two atoms cannot unify, hence, we skip this instance..
                continue;

            unify_atom *u_res = new unify_atom(slv, *this, atm, t_atm, {lit(atm.get_sigma(), false), t_atm.get_sigma(), eq_v});
            assert(slv.get_sat_core().value(u_res->get_rho()) != False);
            add_resolver(*u_res);
            slv.new_causal_link(target, *u_res);
            slv.set_estimated_cost(*u_res, target.get_estimated_cost());
        }
    }

    if (is_fact)
        add_resolver(*new activate_fact(slv, *this, atm));
    else
        add_resolver(*new activate_goal(slv, *this, atm));
}

atom_flaw::activate_fact::activate_fact(solver &slv, atom_flaw &f, atom &a) : resolver(slv, 0, f), atm(a) {}
atom_flaw::activate_fact::~activate_fact() {}

void atom_flaw::activate_fact::apply() { slv.get_sat_core().new_clause({lit(get_rho(), false), atm.get_sigma()}); }

atom_flaw::activate_goal::activate_goal(solver &slv, atom_flaw &f, atom &a) : resolver(slv, 1, f), atm(a) {}
atom_flaw::activate_goal::~activate_goal() {}

void atom_flaw::activate_goal::apply()
{
    slv.get_sat_core().new_clause({lit(get_rho(), false), atm.get_sigma()});
    static_cast<const predicate &>(atm.get_type()).apply_rule(atm);
}

atom_flaw::unify_atom::unify_atom(solver &slv, atom_flaw &f, atom &atm, atom &trgt, const std::vector<lit> &unif_lits) : resolver(slv, 1, f), atm(atm), trgt(trgt), unif_lits(unif_lits) {}
atom_flaw::unify_atom::~unify_atom() {}

void atom_flaw::unify_atom::apply()
{
    for (const auto &v : unif_lits)
        slv.get_sat_core().new_clause({lit(get_rho(), false), v});
}
} // namespace ratio