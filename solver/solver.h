#pragma once

#include "core.h"
#ifdef BUILD_GUI
#define FIRE_NEW_FLAW(f) fire_new_flaw(f)
#define FIRE_FLAW_STATE_CHANGED(f) fire_flaw_state_changed(f)
#define FIRE_FLAW_COST_CHANGED(f) fire_flaw_cost_changed(f)
#define FIRE_CURRENT_FLAW(f) fire_current_flaw(f)
#define FIRE_NEW_RESOLVER(r) fire_new_resolver(r)
#define FIRE_RESOLVER_STATE_CHANGED(r) fire_resolver_state_changed(r)
#define FIRE_RESOLVER_COST_CHANGED(r) fire_resolver_cost_changed(r)
#define FIRE_CURRENT_RESOLVER(r) fire_current_resolver(r)
#define FIRE_CAUSAL_LINK_ADDED(f, r) fire_causal_link_added(f, r)
#define FIRE_STATE_CHANGED() fire_state_changed()
#else
#define FIRE_NEW_FLAW(f)
#define FIRE_FLAW_STATE_CHANGED(f)
#define FIRE_FLAW_COST_CHANGED(f)
#define FIRE_CURRENT_FLAW(f)
#define FIRE_NEW_RESOLVER(r)
#define FIRE_RESOLVER_STATE_CHANGED(r)
#define FIRE_RESOLVER_COST_CHANGED(r)
#define FIRE_CURRENT_RESOLVER(r)
#define FIRE_CAUSAL_LINK_ADDED(f, r)
#define FIRE_SOLUTION_FOUND()
#define FIRE_STATE_CHANGED()
#endif

#define START "start"
#define END "end"

namespace ratio
{

class flaw;
class resolver;
class atom_flaw;
class composite_flaw;
class smart_type;

class solver : public core, private smt::theory
{
  friend class flaw;
  friend class resolver;
  friend class atom_flaw;
  friend class composite_flaw;
  friend class smart_type;
#ifdef BUILD_GUI
  friend class solver_listener;
#endif

public:
  solver();
  solver(const solver &orig) = delete;
  virtual ~solver();

  void init(); // initializes the solver..

  expr new_enum(const type &tp, const std::unordered_set<item *> &allowed_vals) override;
  atom_flaw &get_reason(const atom &atm) const { return *reason.at(&atm); } // returns the flaw which has given rise to the atom..

  void solve() override; // solves the given problem..

private:
  void build_graph();               // builds the planning graph..
  void solve_inconsistencies();     // checks whether the types have some inconsistency..
  void expand_flaw(flaw &f);        // expands the given flaw into the planning graph..
  void apply_resolver(resolver &r); // applies the given resolver into the planning graph..

  void add_layer();         // adds a layer to the current planning graph..
  void increase_accuracy(); // increases the heuristic accuracy by one..

#ifdef DEFERRABLE_FLAWS
  bool is_deferrable(flaw &f); // checks whether the given flaw is deferrable..
#endif
#ifdef GRAPH_PRUNING
  void check_graph(); // checks whether the planning graph can be used for the search..
#endif

  void new_fact(atom &atm) override;                                      // creates a new fact token..
  void new_goal(atom &atm) override;                                      // creates a new goal token..
  void new_disjunction(context &d_ctx, const disjunction &disj) override; // creates a new disjunction..

  bool propagate(const smt::lit &p, std::vector<smt::lit> &cnfl) override;
  bool check(std::vector<smt::lit> &cnfl) override;
  void push() override;
  void pop() override;

  void new_flaw(flaw &f);
  void new_resolver(resolver &r);
  void new_causal_link(flaw &f, resolver &r);

  void set_estimated_cost(resolver &r, const smt::rational &cst);     // sets the estimated cost of the given resolver, propagating it to other resolvers..
  static const smt::rational evaluate(const std::vector<flaw *> &fs); // evaluates, together, the given vector of flaws..
  flaw *select_flaw();                                                // selects the most promising (i.e. the most expensive one) flaw from the 'flaws' set, returns a nullptr if there are no more active flaws..

  void set_new_gamma();
  void take_decision(const smt::lit &ch);
  void next();
  void record(const std::vector<smt::lit> &clause) override;
  std::vector<smt::lit> get_trail() const; // returns the current trail: a vector of literals representing the decisions, in chronological order, that have been taken so far..

private:
  resolver *res = nullptr;                                    // the current resolver (i.e. the cause for the new flaws)..
  std::unordered_set<flaw *> flaws;                           // the currently active flaws..
  std::vector<flaw *> pending_flaws;                          // the currently pending (i.e. those that have not yet been initialized) flaws..
  std::unordered_map<smt::var, std::vector<flaw *>> phis;     // the phi variables (propositional variable to flaws) of the flaws..
  std::unordered_map<smt::var, std::vector<resolver *>> rhos; // the rho variables (propositional variable to resolver) of the resolvers..
  std::deque<flaw *> flaw_q;                                  // the flaw queue (for the graph building procedure)..
  std::unordered_map<const atom *, atom_flaw *> reason;       // the reason for having introduced an atom..

  struct layer
  {

    layer(const smt::lit &dec) : decision(dec) {}

    const smt::lit decision;                                   // the decision which introduced the new layer..
    std::unordered_map<resolver *, smt::rational> old_r_costs; // the old estimated resolvers' costs..
    std::unordered_map<flaw *, smt::rational> old_f_costs;     // the old estimated flaws' costs..
    std::unordered_set<flaw *> new_flaws;                      // the just activated flaws..
    std::unordered_set<flaw *> solved_flaws;                   // the just solved flaws..
  };
  std::vector<layer> trail;                                // the list of applied resolvers, with the associated changes made, in chronological order..
  smt::var gamma;                                          // this variable represents the validity of the current graph..
  unsigned short accuracy = MIN_ACCURACY;                  // the current heuristic accuracy..
  static const unsigned short max_accuracy = MAX_ACCURACY; // the maximum heuristic accuracy..
#ifdef BUILD_GUI
private:
  std::vector<solver_listener *> listeners; // the solver listeners..

  void fire_new_flaw(const flaw &f) const;
  void fire_flaw_state_changed(const flaw &f) const;
  void fire_flaw_cost_changed(const flaw &f) const;
  void fire_current_flaw(const flaw &f) const;
  void fire_new_resolver(const resolver &r) const;
  void fire_resolver_state_changed(const resolver &r) const;
  void fire_resolver_cost_changed(const resolver &r) const;
  void fire_current_resolver(const resolver &r) const;
  void fire_causal_link_added(const flaw &f, const resolver &r) const;
  void fire_state_changed() const;
#endif
};
} // namespace ratio
