#pragma once

#include "smart_type.h"
#include "constructor.h"
#include "graph.h"

#define STATE_VARIABLE_NAME "StateVariable"

namespace ratio
{

class state_variable : public smart_type
{
public:
  state_variable(solver &slv);
  state_variable(const state_variable &orig) = delete;
  virtual ~state_variable();

private:
  std::vector<flaw *> get_flaws() override;

  void new_predicate(predicate &pred) override;
  void new_fact(atom_flaw &f) override;
  void new_goal(atom_flaw &f) override;
  void store_variables(atom &atm0, atom &atm1);

  // the state-variable constructor..
  class sv_constructor : public constructor
  {
  public:
    sv_constructor(state_variable &sv);
    sv_constructor(sv_constructor &&) = delete;
    virtual ~sv_constructor();
  };

  // the atom listener for the state-variable..
  class sv_atom_listener : public atom_listener
  {
  public:
    sv_atom_listener(state_variable &sv, atom &atm);
    sv_atom_listener(sv_atom_listener &&) = delete;
    virtual ~sv_atom_listener();

  private:
    void something_changed();

    void sat_value_change(const smt::var &) override { something_changed(); }
    void lra_value_change(const smt::var &) override { something_changed(); }
    void ov_value_change(const smt::var &) override { something_changed(); }

  protected:
    state_variable &sv;
  };

  // the flaw (i.e. two or more temporally overlapping atoms on the same state-variable instance) that can arise from a state-variable..
  class sv_flaw : public flaw
  {
    friend class state_variable;

  public:
    sv_flaw(state_variable &sv, const std::set<atom *> &overlapping_atoms);
    sv_flaw(sv_flaw &&) = delete;
    virtual ~sv_flaw();

#ifdef BUILD_GUI
    std::string get_label() const override;
#endif

  private:
    std::vector<std::pair<smt::lit, double>> evaluate(); // evaluates the flaw returning the current available choices and their commit..
    void compute_resolvers() override;

  private:
    state_variable &sv;
    const std::set<atom *> overlapping_atoms;
  };

  // a resolver for temporally ordering atoms..
  class order_resolver : public resolver
  {
  public:
    order_resolver(sv_flaw &flw, const smt::var &r, const atom &before, const atom &after);
    order_resolver(const order_resolver &that) = delete;
    virtual ~order_resolver();

#ifdef BUILD_GUI
    std::string get_label() const override;
#endif

  private:
    void apply() override;

  private:
    const atom &before;
    const atom &after;
  };

  // a resolver for placing atoms on a specific state-variable..
  class place_resolver : public resolver
  {
  public:
    place_resolver(sv_flaw &flw, atom &atm, item &itm);
    place_resolver(const place_resolver &that) = delete;
    virtual ~place_resolver();

#ifdef BUILD_GUI
    std::string get_label() const override;
#endif

  private:
    void apply() override;

  private:
    atom &atm;
    item &itm;
  };

private:
  std::set<item *> to_check;                                // the state-variable instances whose atoms have changed..
  std::map<atom *, std::map<atom *, smt::lit>> leqs;        // all the possible ordering constraints..
  std::map<std::set<atom *>, sv_flaw *> sv_flaws;           // the state-variable flaws found so far..
  std::vector<std::pair<atom *, sv_atom_listener *>> atoms; // we store, for each atom, its atom listener..
};
} // namespace ratio
