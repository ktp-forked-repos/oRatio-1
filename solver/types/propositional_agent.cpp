#include "propositional_agent.h"
#include "solver.h"
#include "atom.h"
#include "atom_flaw.h"

namespace ratio
{

propositional_agent::propositional_agent(solver &slv) : smart_type(slv, slv, PROPOSITIONAL_AGENT_NAME) { new_constructors({new agnt_constructor(*this)}); }
propositional_agent::~propositional_agent() {}

void propositional_agent::get_flaws(std::vector<flaw *> &flaws) {}

void propositional_agent::new_fact(atom_flaw &) { throw std::logic_error("it is not possible to define facts on propositional agents.."); }

void propositional_agent::new_goal(atom_flaw &f)
{
    atom &atm = f.get_atom();
    atoms.push_back({&atm, new agnt_atom_listener(*this, atm)});
    to_check.insert(&atm);
}

propositional_agent::agnt_constructor::agnt_constructor(propositional_agent &agnt) : constructor(agnt.get_solver(), agnt, {}, {}, {}) {}
propositional_agent::agnt_constructor::~agnt_constructor() {}

propositional_agent::agnt_atom_listener::agnt_atom_listener(propositional_agent &agnt, atom &atm) : atom_listener(atm), agnt(agnt) {}
propositional_agent::agnt_atom_listener::~agnt_atom_listener() {}
void propositional_agent::agnt_atom_listener::something_changed() { agnt.to_check.insert(&atm); }

propositional_agent::agnt_flaw::agnt_flaw(solver &s, const std::set<atom *> &overlapping_atoms) : flaw(s, smart_type::get_resolvers(s, overlapping_atoms)), overlapping_atoms(overlapping_atoms) {}
propositional_agent::agnt_flaw::~agnt_flaw() {}
void propositional_agent::agnt_flaw::compute_resolvers() {}

#ifdef BUILD_GUI
std::string propositional_agent::agnt_flaw::get_label() const
{
    return "agent-flaw";
}
#endif

propositional_agent::order_resolver::order_resolver(solver &slv, const smt::var &r, agnt_flaw &f, const atom &before, const atom &after) : resolver(slv, r, 0, f), before(before), after(after)
{
}
propositional_agent::order_resolver::~order_resolver() {}
void propositional_agent::order_resolver::apply() {}

#ifdef BUILD_GUI
std::string propositional_agent::order_resolver::get_label() const
{
    return "ρ" + std::to_string(get_rho()) + " σ" + std::to_string(before.get_sigma()) + " <= σ" + std::to_string(after.get_sigma());
}
#endif

propositional_agent::displace_resolver::displace_resolver(solver &slv, agnt_flaw &f, const atom &a0, const atom &a1, const smt::lit &neq_lit) : resolver(slv, 0, f), a0(a0), a1(a1), neq_lit(neq_lit)
{
}
propositional_agent::displace_resolver::~displace_resolver() {}
void propositional_agent::displace_resolver::apply() { slv.get_sat_core().new_clause({smt::lit(get_rho(), false), neq_lit}); }

#ifdef BUILD_GUI
std::string propositional_agent::displace_resolver::get_label() const
{
    return "ρ" + std::to_string(get_rho()) + " displ σ" + std::to_string(a0.get_sigma()) + ".τ != σ" + std::to_string(a1.get_sigma()) + ".τ";
}
#endif
} // namespace ratio