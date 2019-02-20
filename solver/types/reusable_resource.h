#pragma once

#include "smart_type.h"
#include "constructor.h"
#include "predicate.h"
#include "graph.h"

#define REUSABLE_RESOURCE_NAME "ReusableResource"
#define REUSABLE_RESOURCE_CAPACITY "capacity"
#define REUSABLE_RESOURCE_USE_PREDICATE_NAME "Use"
#define REUSABLE_RESOURCE_USE_AMOUNT_NAME "amount"

namespace ratio
{

class reusable_resource : public smart_type
{
public:
  reusable_resource(solver &slv);
  reusable_resource(const reusable_resource &orig) = delete;
  virtual ~reusable_resource();

private:
  void get_flaws(std::vector<flaw *> &flaws) override;

  void new_predicate(predicate &) override { throw std::logic_error("it is not possible to define predicates on a reusable resource.."); }
  void new_fact(atom_flaw &f) override;
  void new_goal(atom_flaw &f) override;
  void store_variables(atom &atm0, atom &atm1);

  // the reusable-resource constructor..
  class rr_constructor : public constructor
  {
  public:
    rr_constructor(reusable_resource &rr);
    rr_constructor(rr_constructor &&) = delete;
    virtual ~rr_constructor();
  };

  // the reusable-resource 'use' predicate..
  class use_predicate : public predicate
  {
  public:
    use_predicate(reusable_resource &rr);
    use_predicate(use_predicate &&) = delete;
    virtual ~use_predicate();
  };

  // the atom listener for the reusable-resource..
  class rr_atom_listener : public atom_listener
  {
  public:
    rr_atom_listener(reusable_resource &rr, atom &atm);
    rr_atom_listener(rr_atom_listener &&) = delete;
    virtual ~rr_atom_listener();

  private:
    void something_changed();

    void sat_value_change(const smt::var &) override { something_changed(); }
    void lra_value_change(const smt::var &) override { something_changed(); }
    void ov_value_change(const smt::var &) override { something_changed(); }

  protected:
    reusable_resource &rr;
  };

  // the flaw (i.e. temporally overlapping atoms on the same reusable-resource instance whose consumption sums up to an amount which is greater than the resource's capacity) that can arise from a state-variable..
  class rr_flaw : public flaw
  {
    friend class reusable_resource;

  public:
    rr_flaw(reusable_resource &rr, const std::set<atom *> &overlapping_atoms);
    rr_flaw(rr_flaw &&) = delete;
    virtual ~rr_flaw();

#ifdef BUILD_GUI
    std::string get_label() const override;
#endif

  private:
    std::vector<std::pair<smt::lit, double>> evaluate(); // evaluates the flaw returning the current available choices and their commit..
    void compute_resolvers() override;

  private:
    reusable_resource &rr;
    const std::set<atom *> overlapping_atoms;
  };

  // a resolver for temporally ordering atoms..
  class order_resolver : public resolver
  {
  public:
    order_resolver(rr_flaw &f, const smt::var &r, const atom &before, const atom &after);
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
    place_resolver(rr_flaw &flw, atom &atm, item &itm);
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
  std::set<item *> to_check;                                // the reusable resources to check for inconsistencies..
  std::map<atom *, std::map<atom *, smt::lit>> leqs;        // all the possible ordering constraints..
  std::vector<std::pair<atom *, rr_atom_listener *>> atoms; // the reusable resources' atoms and their listeners..
  std::map<std::set<atom *>, rr_flaw *> rr_flaws;           // the reusable resource flaws found so far..
};
} // namespace ratio
