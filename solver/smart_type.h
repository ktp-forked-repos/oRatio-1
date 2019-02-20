#pragma once

#include "type.h"
#include "sat_value_listener.h"
#include "lra_value_listener.h"
#include "ov_value_listener.h"

namespace ratio
{

class solver;
class atom;
class flaw;
class atom_flaw;
class resolver;

class smart_type : public type
{
  friend class solver;

public:
  smart_type(solver &slv, scope &scp, const std::string &name);
  smart_type(const smart_type &that) = delete;
  virtual ~smart_type();

  solver &get_solver() const { return slv; }

private:
  virtual void get_flaws(std::vector<flaw *> &flaws) = 0;
  virtual void new_fact(atom_flaw &);
  virtual void new_goal(atom_flaw &);

protected:
  void set_ni(const smt::var &v); // temporally sets the solver's 'ni' variable..
  void restore_ni();              // restores the solver's 'ni' variable..

  void take_decision(const smt::lit &ch);  // takes the given decision..
  std::vector<smt::lit> get_trail() const; // returns the current trail: a vector of literals representing the decisions, in chronological order, that have been taken so far..

  void next();
  void record(const std::vector<smt::lit> &clause);

  static std::vector<resolver *> get_resolvers(solver &slv, const std::set<atom *> &atms); // returns the vector of resolvers which has given rise to the given atoms..

private:
  solver &slv;
};

class atom_listener : public smt::sat_value_listener, public smt::lra_value_listener, public smt::ov_value_listener
{
public:
  atom_listener(atom &atm);
  atom_listener(const atom_listener &that) = delete;
  virtual ~atom_listener();

protected:
  atom &atm;
};
} // namespace ratio