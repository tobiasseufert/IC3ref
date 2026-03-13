/*********************************************************************
Copyright (c) 2013, Aaron Bradley

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#include <iostream>

#include "Model.h"
#include "SimpSolver.h"
#include "Vec.h"

Minisat::Var Var::gvi = 0;
size_t DrVar::num_std_vars = 0;

Model::~Model() {
  if (inits) delete inits;
  if (sslv) delete sslv;
  if (sslv_dr) delete sslv_dr;
}

void Model::addVar(const Var & v) {
  assert (primesUnlocked);
  vars.push_back(v);
  DrVar::incVars();
}

const Var & Model::primeVar(const Var & v, Minisat::SimpSolver * slv) {
  // var for false
  if (v.index() == 0) return v;
  // latch or PI
  if (v.index() < reps)
    return vars[primes+v.index()-inputs];
  // AND lit
  assert (v.index() >= reps && v.index() < primes);
  // created previously?
  IndexMap::const_iterator i = primedAnds.find(v.index());
  size_t index;
  if (i == primedAnds.end()) {
    // no, so make sure the model hasn't been locked
    assert (primesUnlocked);
    // create a primed version
    stringstream ss;
    ss << v.name() << "'";
    index = vars.size();
    addVar(Var(ss.str()));
    if (slv) {
      Minisat::Var _v = slv->newVar();
      if (_v != vars.back().var()) {
        throw runtime_error(string("Priming variable " + v.name() + " failed."));
      }
    }
    assert (vars.back().index() == index);
    primedAnds.insert(IndexMap::value_type(v.index(), index));
  }
  else
    index = i->second;
  return vars[index];
}

Minisat::Solver * Model::newSolver() const {
  Minisat::Solver * slv = new Minisat::Solver();
  // load all variables to maintain alignment
  for (size_t i = 0; i < vars.size(); ++i) {
    Minisat::Var nv = slv->newVar();
    if (nv != vars[i].var()) {
      throw runtime_error("Variable alignment in solvers broken.");
    }
  }
  return slv;
}
Minisat::Solver * Model::newDrSolver() const {
  if (primesUnlocked) {
    throw runtime_error("Dual rail variables were supposed to be created, but there might still be new variables of the actual problem.");
  }
  Minisat::Solver * slv = new Minisat::Solver();
  slv->phase_saving = 2;
  // load all variables to maintain alignment
  // ask the solver to decide (0,0) by default (except for inputs)
  slv->newVar(); // constant 0/1
  for (size_t i = 1; i < vars.size(); ++i) {
    slv->newVar(Minisat::l_True); // True equals to 0 ... Minisat interface issue there, but ok.
    Minisat::Var nv_dual = slv->newVar(Minisat::l_True);

    if ((nv_dual / 2) != vars[i].var()) {
      throw runtime_error("Variable alignment in solvers broken.");
    }
  }
  return slv;
}

void Model::loadTransitionRelation(Minisat::Solver & slv, bool withConstraints) {
  if (!sslv) {
    // create a simplified CNF version of (this slice of) the TR
    sslv = new Minisat::SimpSolver();
    // introduce all variables to maintain alignment
    for (size_t i = 0; i < vars.size(); ++i) {
      Minisat::Var nv = sslv->newVar();      
      if (nv != vars[i].var()) {
        throw runtime_error("Variable alignment in solvers broken.");
      }
    }
    // freeze inputs, latches, and special nodes (and primed forms)
    for (VarVec::const_iterator i = beginInputs(); i != endInputs(); ++i) {
      sslv->setFrozen(i->var(), true);
      sslv->setFrozen(primeVar(*i).var(), true);
    }
    for (VarVec::const_iterator i = beginLatches(); i != endLatches(); ++i) {
      sslv->setFrozen(i->var(), true);
      sslv->setFrozen(primeVar(*i).var(), true);
    }
    sslv->setFrozen(varOfLit(error()).var(), true);
    sslv->setFrozen(varOfLit(primedError()).var(), true);
    for (LitVec::const_iterator i = constraints.begin(); 
         i != constraints.end(); ++i) {
      Var v = varOfLit(*i);
      sslv->setFrozen(v.var(), true);
      sslv->setFrozen(primeVar(v).var(), true);
    }
    // initialize with roots of required formulas
    LitSet require;  // unprimed formulas
    for (VarVec::const_iterator i = beginLatches(); i != endLatches(); ++i)
      require.insert(nextStateFn(*i));
    require.insert(_error);
    require.insert(constraints.begin(), constraints.end());
    LitSet prequire; // for primed formulas; always subset of require
    prequire.insert(_error);
    prequire.insert(constraints.begin(), constraints.end());
    // traverse AIG backward
    for (AigVec::const_reverse_iterator i = aig.rbegin(); 
         i != aig.rend(); ++i) {
      // skip if this row is not required
      if (require.find(i->lhs) == require.end() 
          && require.find(~i->lhs) == require.end())
        continue;
      // encode into CNF
      sslv->addClause(~i->lhs, i->rhs0);
      sslv->addClause(~i->lhs, i->rhs1);
      sslv->addClause(~i->rhs0, ~i->rhs1, i->lhs);
      // require arguments
      require.insert(i->rhs0);
      require.insert(i->rhs1);
      // primed: skip if not required
      if (prequire.find(i->lhs) == prequire.end()
          && prequire.find(~i->lhs) == prequire.end())
        continue;
      // encode PRIMED form into CNF
      Minisat::Lit r0 = primeLit(i->lhs, sslv), 
        r1 = primeLit(i->rhs0, sslv), 
        r2 = primeLit(i->rhs1, sslv);
      sslv->addClause(~r0, r1);
      sslv->addClause(~r0, r2);
      sslv->addClause(~r1, ~r2, r0);
      // require arguments
      prequire.insert(i->rhs0);
      prequire.insert(i->rhs1);
    }
    // assert literal for true
    sslv->addClause(btrue());
    // assert ~error
    sslv->addClause(~_error);
    // assert l' = f for each latch l
    for (VarVec::const_iterator i = beginLatches(); i != endLatches(); ++i) {
      Minisat::Lit platch = primeLit(i->lit(false)), f = nextStateFn(*i);
      sslv->addClause(~platch, f);
      sslv->addClause(~f, platch);
    }
    sslv->eliminate(true);
  }
  // load the clauses from the simplified context
  while (slv.nVars() < sslv->nVars()) slv.newVar();
  for (Minisat::ClauseIterator c = sslv->clausesBegin(); 
       c != sslv->clausesEnd(); ++c) {
    const Minisat::Clause & cls = *c;
    Minisat::vec<Minisat::Lit> cls_;
    for (int i = 0; i < cls.size(); ++i)
      cls_.push(cls[i]);
    slv.addClause_(cls_);
  }
  for (Minisat::TrailIterator c = sslv->trailBegin(); 
       c != sslv->trailEnd(); ++c)
    slv.addClause(*c);
  if (withConstraints)
    for (LitVec::const_iterator i = constraints.begin(); 
         i != constraints.end(); ++i) {
      slv.addClause(*i);
      slv.addClause(primeLit(*i));
    }
}

void Model::initSimpDrContext() {
  if (!sslv_dr) {
    // create a simplified CNF version of (this slice of) the TR
    sslv_dr = new Minisat::SimpSolver();
    // introduce all variables to maintain alignment
    sslv_dr->newVar();
    for (size_t i = 1; i < vars.size(); ++i) {
      sslv_dr->newVar();
      Minisat::Var nv_dual = sslv_dr->newVar();      
      if ((nv_dual / 2) != vars[i].var()) {
        throw runtime_error("Variable alignment in solvers broken.");
      }
    }
    // freeze inputs, latches, and special nodes (and primed forms)
    for (VarVec::const_iterator i = beginInputs(); i != endInputs(); ++i) {
      FreezeDrVar(i->var(), *sslv_dr);
      FreezeDrVar(primeVar(*i).var(), *sslv_dr);
    }
    for (VarVec::const_iterator i = beginLatches(); i != endLatches(); ++i) {
      FreezeDrVar(i->var(), *sslv_dr);
      FreezeDrVar(primeVar(*i).var(), *sslv_dr);
    }
    FreezeDrVar(varOfLit(error()).var(), *sslv_dr);
    FreezeDrVar(varOfLit(primedError()).var(), *sslv_dr);
    for (LitVec::const_iterator i = constraints.begin(); 
         i != constraints.end(); ++i) {
      Var v = varOfLit(*i);
      FreezeDrVar(v.var(), *sslv_dr);
      FreezeDrVar(primeVar(v).var(), *sslv_dr);
    }
    // dual-rail (1,1) encoding forbidden
    for (size_t i = 1; i < vars.size(); ++i) { // ignore constants
      const Var& curr_var = vars[i];
#ifndef NDEBUG    
      Minisat::Var dual_rail_correspondent = curr_var.var() + vars.back().var();
#endif    
      DrVar dr_var{curr_var.var()};
      assert (dual_rail_correspondent == dr_var.GetCorres());
      dr_var.AddOneOneExclusionCl(*sslv_dr);
    }
    // initialize with roots of required formulas
    LitSet require;  // unprimed formulas
    for (VarVec::const_iterator i = beginLatches(); i != endLatches(); ++i)
      require.insert(nextStateFn(*i));
    require.insert(_error);
    require.insert(constraints.begin(), constraints.end());
    LitSet prequire; // for primed formulas; always subset of require
    prequire.insert(_error);
    prequire.insert(constraints.begin(), constraints.end());
    // traverse AIG backward
    for (AigVec::const_reverse_iterator i = aig.rbegin(); 
         i != aig.rend(); ++i) {
      // skip if this row is not required
      if (require.find(i->lhs) == require.end() 
          && require.find(~i->lhs) == require.end())
        continue;
      // encode into CNF
      //loadDrAndTseitin(*sslv_dr, *i);
      loadDrAndForgetful(*sslv_dr, *i);
      // require arguments
      require.insert(i->rhs0);
      require.insert(i->rhs1);
      // primed: skip if not required
      if (prequire.find(i->lhs) == prequire.end()
          && prequire.find(~i->lhs) == prequire.end())
        continue;
      // encode PRIMED form into CNF
      //loadDrAndTseitin(*sslv_dr, *i, true);
      loadDrAndForgetful(*sslv_dr, *i, true);
      // require arguments
      prequire.insert(i->rhs0);
      prequire.insert(i->rhs1);
    }
    // assert literal for true
    sslv_dr->addClause(btrue());
    // assert ~error
    AddDrClause(~_error, *sslv_dr);
    // assert l' = f for each latch l
    for (VarVec::const_iterator i = beginLatches(); i != endLatches(); ++i) {
      Minisat::Lit platch = primeLit(i->lit(false)), f = nextStateFn(*i);
      AddDrEquivGate(*sslv_dr, platch, f);
    }
    sslv_dr->eliminate(true);
  }
}

void Model::AddDrEquivGate(Minisat::Solver& slv, Minisat::Lit equiv1, Minisat::Lit equiv2) const {
  const bool equiv1_is_btrue = (equiv1 == btrue());
  const bool equiv1_is_bfalse = (equiv1 == bfalse());
  const bool equiv2_is_btrue = (equiv2 == btrue());
  const bool equiv2_is_bfalse = (equiv2 == bfalse());

  const bool equiv1_is_const = equiv1_is_btrue || equiv1_is_bfalse;
  const bool equiv2_is_const = equiv2_is_btrue || equiv2_is_bfalse;

  if (equiv1_is_const && equiv2_is_const) {
    if (equiv1_is_btrue != equiv2_is_btrue)
      slv.addEmptyClause();
    return;
  }

  if (equiv1_is_const) {
    if (equiv1_is_btrue)
      AddDrClause(equiv2, slv);
    else
      AddDrClause(~equiv2, slv);
    return;
  }

  if (equiv2_is_const) {
    if (equiv2_is_btrue)
      AddDrClause(equiv1, slv);
    else
      AddDrClause(~equiv1, slv);
    return;
  }

  AddDrEquivGateNoConst(slv, equiv1, equiv2);
}

void Model::AddDrEquivGateNoConst(Minisat::Solver& slv, Minisat::Lit equiv1, Minisat::Lit equiv2) const {
  DrLit equiv1_dr{Minisat::var(equiv1)}, 
        equiv2_dr{Minisat::var(equiv2)};
  
  Minisat::Lit equiv1_0, equiv1_1;
  Minisat::Lit equiv2_0, equiv2_1;

  if (Minisat::sign(equiv1)) { // evaluate NOT
    equiv1_0 = equiv1_dr.One();
    equiv1_1 = equiv1_dr.Zero();
  } else {
    equiv1_0 = equiv1_dr.Zero();
    equiv1_1 = equiv1_dr.One();
  }
  if (Minisat::sign(equiv2)) { // evaluate NOT
    equiv2_0 = equiv2_dr.One();
    equiv2_1 = equiv2_dr.Zero();
  } else {
    equiv2_0 = equiv2_dr.Zero();
    equiv2_1 = equiv2_dr.One();
  }

  // add the clauses accordingly
  // equiv1^(0) == equiv2^(0)
  slv.addClause(~equiv1_0, equiv2_0);
  slv.addClause(equiv1_0, ~equiv2_0);

  // equiv1^(1) == equiv2^(1)
  slv.addClause(~equiv1_1, equiv2_1);
  slv.addClause(equiv1_1, ~equiv2_1);
}

void Model::loadDrTransitionRelation(Minisat::Solver & slv, bool withConstraints) {
  assert (!primesUnlocked); // guarantee that the size of vars won't change anymore
  initSimpDrContext();
  // load the clauses from the simplified context
  if (slv.nVars() < sslv_dr->nVars()) {
    throw runtime_error{"Something off with dual rail variable alignment."};
  }
  for (Minisat::ClauseIterator c = sslv_dr->clausesBegin(); 
       c != sslv_dr->clausesEnd(); ++c) {
    const Minisat::Clause & cls = *c;
    Minisat::vec<Minisat::Lit> cls_;
    for (int i = 0; i < cls.size(); ++i)
      cls_.push(cls[i]);
    slv.addClause_(cls_);
  }
  for (Minisat::TrailIterator c = sslv_dr->trailBegin(); 
       c != sslv_dr->trailEnd(); ++c)
    slv.addClause(*c);
  if (withConstraints)
    for (LitVec::const_iterator i = constraints.begin(); 
         i != constraints.end(); ++i) {
      AddDrClause(primeLit(*i), slv);
      AddDrClause(*i, slv);
    }
}

void Model::loadInitialCondition(Minisat::Solver & slv) const {
  slv.addClause(btrue());
  for (LitVec::const_iterator i = init.begin(); i != init.end(); ++i)
    slv.addClause(*i);
  if (constraints.empty())
    return;
  // impose invariant constraints on initial states (AIGER 1.9)
  LitSet require;
  require.insert(constraints.begin(), constraints.end());
  for (AigVec::const_reverse_iterator i = aig.rbegin(); i != aig.rend(); ++i) {
    // skip if this (*i) is not required
    if (require.find(i->lhs) == require.end() 
        && require.find(~i->lhs) == require.end())
      continue;
    // encode into CNF
    slv.addClause(~i->lhs, i->rhs0);
    slv.addClause(~i->lhs, i->rhs1);
    slv.addClause(~i->rhs0, ~i->rhs1, i->lhs);
    // require arguments
    require.insert(i->rhs0);
    require.insert(i->rhs1);
  }
  for (LitVec::const_iterator i = constraints.begin(); 
       i != constraints.end(); ++i)
    slv.addClause(*i);
}

/* Implementation of 01X-AND:
    in1   in2   out
    0 0   0 0   0 0   X & X = X
    0 0   0 1   0 0
    0 0   1 0   1 0
    ---------------
    0 1   0 0   0 0   1 & X = X
    0 1   0 1   0 1
    0 1   1 0   1 0
    ---------------
    1 0   0 0   1 0   0 & X = 0
    1 0   0 1   1 0
    1 0   1 0   1 0
*/

/* Implementation of 01X-NOT:
    ~(in1, in2) = (in2, in1)
*/
void Model::loadDrAndTseitin(Minisat::Solver& slv, const AigRow& and_gate, bool prime) {
  Minisat::Lit rhs0 = prime? primeLit(and_gate.rhs0) : and_gate.rhs0;
  Minisat::Lit rhs1 = prime? primeLit(and_gate.rhs1) : and_gate.rhs1;

  const bool rhs0_is_btrue = (rhs0 == btrue());
  const bool rhs0_is_bfalse = (rhs0 == bfalse());
  const bool rhs1_is_btrue = (rhs1 == btrue());
  const bool rhs1_is_bfalse = (rhs1 == bfalse());

  const bool rhs0_is_const = rhs0_is_btrue || rhs0_is_bfalse;
  const bool rhs1_is_const = rhs1_is_btrue || rhs1_is_bfalse;

  if (!rhs0_is_const && !rhs1_is_const) {
    loadDrAndTseitinNoConst(slv, and_gate, prime);
    return;
  }

  Minisat::Lit lhs = prime? primeLit(and_gate.lhs) : and_gate.lhs;
  assert (!Minisat::sign(lhs)); // by AIGER design

  if (rhs0_is_bfalse || rhs1_is_bfalse) {
    AddDrEquivGate(slv, lhs, bfalse());
    return;
  }
  if (rhs0_is_btrue && rhs1_is_btrue) {
    AddDrEquivGate(slv, lhs, btrue());
    return;
  }
  if (rhs0_is_btrue) {
    AddDrEquivGate(slv, lhs, rhs1);
    return;
  }

  AddDrEquivGate(slv, lhs, rhs0);
}

void Model::loadDrAndForgetful(Minisat::Solver& slv, const AigRow& and_gate, bool prime) {
  Minisat::Lit lhs, rhs0, rhs1;
  lhs = prime? primeLit(and_gate.lhs) : and_gate.lhs;
  rhs0 = prime? primeLit(and_gate.rhs0) : and_gate.rhs0;
  rhs1 = prime? primeLit(and_gate.rhs1) : and_gate.rhs1;

  DrLit lhs_dr{Minisat::var(lhs)};
  
  Minisat::Lit rhs0_0, rhs1_0;
  Minisat::Lit rhs0_1, rhs1_1;

  auto eval_rhs = [this](Minisat::Lit rhs, Minisat::Lit& rhs_0, Minisat::Lit& rhs_1) {
    // Constant inputs have fixed truth values and must not be dual-railed.
    if (rhs == btrue()) {
      rhs_0 = bfalse();
      rhs_1 = btrue();
      return;
    }
    if (rhs == bfalse()) {
      rhs_0 = btrue();
      rhs_1 = bfalse();
      return;
    }

    DrLit rhs_dr{Minisat::var(rhs)};
    if (Minisat::sign(rhs)) { // evaluate NOT
      rhs_0 = rhs_dr.One();
      rhs_1 = rhs_dr.Zero();
    } else {
      rhs_0 = rhs_dr.Zero();
      rhs_1 = rhs_dr.One();
    }
  };

  assert (!Minisat::sign(and_gate.lhs)); // by AIGER design
  eval_rhs(rhs0, rhs0_0, rhs0_1);
  eval_rhs(rhs1, rhs1_0, rhs1_1);
  
  slv.addClause(rhs0_0, rhs1_0, ~(lhs_dr.Zero()));
  slv.addClause(rhs1_1, ~(lhs_dr.One()));
  slv.addClause(rhs0_1, ~(lhs_dr.One()));
}

void Model::loadDrAndTseitinNoConst(Minisat::Solver& slv, const AigRow& and_gate, bool prime) {
  Minisat::Lit lhs, rhs0, rhs1;
  lhs = prime? primeLit(and_gate.lhs) : and_gate.lhs;
  rhs0 = prime? primeLit(and_gate.rhs0) : and_gate.rhs0;
  rhs1 = prime? primeLit(and_gate.rhs1) : and_gate.rhs1;
    
  DrLit lhs_dr{Minisat::var(lhs)}, 
        rhs0_dr{Minisat::var(rhs0)}, 
        rhs1_dr{Minisat::var(rhs1)};
  
  Minisat::Lit rhs0_0, rhs1_0;
  Minisat::Lit rhs0_1, rhs1_1;

  assert (!Minisat::sign(and_gate.lhs)); // by AIGER design
  if (Minisat::sign(and_gate.rhs0)) { // evaluate NOT
    rhs0_0 = rhs0_dr.One();
    rhs0_1 = rhs0_dr.Zero();
  } else {
    rhs0_0 = rhs0_dr.Zero();
    rhs0_1 = rhs0_dr.One();
  }
  if (Minisat::sign(and_gate.rhs1)) { // evaluate NOT
    rhs1_0 = rhs1_dr.One();
    rhs1_1 = rhs1_dr.Zero();
  } else {
    rhs1_0 = rhs1_dr.Zero();
    rhs1_1 = rhs1_dr.One();
  }
  
  loadAndTseitin(slv, {~(lhs_dr.Zero()), ~(rhs0_0), ~(rhs1_0)}); // OR of zeros
  loadAndTseitin(slv, {lhs_dr.One(), rhs0_1, rhs1_1}); // AND of ones
}

void Model::loadAndTseitin(Minisat::Solver& slv, AigRow&& and_gate) const {
  slv.addClause(~and_gate.lhs, and_gate.rhs0);
  slv.addClause(~and_gate.lhs, and_gate.rhs1);
  slv.addClause(~and_gate.rhs0, ~and_gate.rhs1, and_gate.lhs);
}

void Model::loadDrInitialCondition(Minisat::Solver & slv) {
  assert (!primesUnlocked);
  slv.addClause(btrue());
  for (LitVec::const_iterator i = init.begin(); i != init.end(); ++i)
    AddDrClause(*i, slv);
  if (constraints.empty())
    return;
  // impose invariant constraints on initial states (AIGER 1.9)
  LitSet require;
  require.insert(constraints.begin(), constraints.end());
  for (AigVec::const_reverse_iterator i = aig.rbegin(); i != aig.rend(); ++i) {
    // skip if this (*i) is not required
    if (require.find(i->lhs) == require.end() 
        && require.find(~i->lhs) == require.end())
      continue;
    // encode into CNF
    loadDrAndTseitin(slv, *i);
    // require arguments
    require.insert(i->rhs0);
    require.insert(i->rhs1);
  }
  for (LitVec::const_iterator i = constraints.begin(); 
       i != constraints.end(); ++i)
    AddDrClause(*i, slv);
}

void Model::loadError(Minisat::Solver & slv) const {
  LitSet require;  // unprimed formulas
  require.insert(_error);
  // traverse AIG backward
  for (AigVec::const_reverse_iterator i = aig.rbegin(); i != aig.rend(); ++i) {
    // skip if this row is not required
    if (require.find(i->lhs) == require.end() 
        && require.find(~i->lhs) == require.end())
      continue;
    // encode into CNF
    slv.addClause(~i->lhs, i->rhs0);
    slv.addClause(~i->lhs, i->rhs1);
    slv.addClause(~i->rhs0, ~i->rhs1, i->lhs);
    // require arguments
    require.insert(i->rhs0);
    require.insert(i->rhs1);
  }
}

bool Model::isInitial(const LitVec & latches) {
  if (constraints.empty()) {
    // an intersection check (AIGER 1.9 w/o invariant constraints)
    if (initLits.empty())
      initLits.insert(init.begin(), init.end());
    for (LitVec::const_iterator i = latches.begin(); i != latches.end(); ++i)
      if (initLits.find(~*i) != initLits.end())
        return false;
    return true;
  }
  else {
    // a full SAT query
    if (!inits) {
      inits = newSolver();
      loadInitialCondition(*inits);
    }
    Minisat::vec<Minisat::Lit> assumps;
    assumps.capacity(latches.size());
    for (LitVec::const_iterator i = latches.begin(); i != latches.end(); ++i)
      assumps.push(*i);
    return inits->solve(assumps);
  }
}

const LitVec& Model::getInitLits() const {
  return this->init;
}

size_t Model::getMaxVar() const {
  return vars.size();
}

size_t Model::getAigMaxVar() const {
  if (aig.size() > 0) {
    return Minisat::var((aig.end() - 1)->lhs);
  } else {
    return 1;
  }
}

// Creates a named variable.
Var var(const aiger_symbol * syms, size_t i, const char prefix, 
        bool prime = false)
{
  const aiger_symbol & sym = syms[i];
  stringstream ss;
  if (sym.name) 
    ss << sym.name;
  else
    ss << prefix << i;
  if (prime) 
    ss << "'";
  return Var(ss.str());
}

Minisat::Lit lit(const VarVec & vars, unsigned int l) {
  return vars[l>>1].lit(aiger_sign(l));
}

void addVar(VarVec& vars, const Var& var) {
  vars.push_back(var);
  DrVar::incVars();
}

Model * modelFromAiger(aiger * aig, unsigned int propertyIndex) {
  VarVec vars(1, Var("false"));
  LitVec init, constraints, nextStateFns;

  // declare primary inputs and latches
  for (size_t i = 0; i < aig->num_inputs; ++i)
    addVar(vars, var(aig->inputs, i, 'i'));
  for (size_t i = 0; i < aig->num_latches; ++i)
    addVar(vars, var(aig->latches, i, 'l'));

  // the AND section
  AigVec aigv;
  for (size_t i = 0; i < aig->num_ands; ++i) {
    // 1. create a representative
    stringstream ss;
    ss << 'r' << i;
    addVar(vars, Var(ss.str()));
    const Var & rep = vars.back();
    // 2. obtain arguments of AND as lits
    Minisat::Lit l0 = lit(vars, aig->ands[i].rhs0);
    Minisat::Lit l1 = lit(vars, aig->ands[i].rhs1);
    // 3. add AIG row
    aigv.push_back(AigRow(rep.lit(false), l0, l1));
  }

  // acquire latches' initial states and next-state functions
  for (size_t i = 0; i < aig->num_latches; ++i) {
    const Var & latch = vars[1+aig->num_inputs+i];
    // initial condition
    unsigned int r = aig->latches[i].reset;
    if (r < 2)
      init.push_back(latch.lit(r == 0));
    // next-state function
    nextStateFns.push_back(lit(vars, aig->latches[i].next));
  }

  // invariant constraints
  for (size_t i = 0; i < aig->num_constraints; ++i)
    constraints.push_back(lit(vars, aig->constraints[i].lit));

  // acquire error from given propertyIndex
  if ((aig->num_bad > 0 && aig->num_bad <= propertyIndex)
      || (aig->num_outputs > 0 && aig->num_outputs <= propertyIndex)) {
    cout << "Bad property index specified." << endl;
    return 0;
  }
  Minisat::Lit err = 
    aig->num_bad > 0 
    ? lit(vars, aig->bad[propertyIndex].lit) 
    : lit(vars, aig->outputs[propertyIndex].lit);

  return new Model(vars, 
                   1, 1 + aig->num_inputs, 
                   1 + aig->num_inputs + aig->num_latches,
                   init, constraints, nextStateFns, err, aigv);
}

DrLit::DrLit(const DrVar& var, DrSign sign)
  : zero(Minisat::mkLit(var.zero, true)),
    one(Minisat::mkLit(var.one, true)) {
  switch (sign) {
  case DrSign::FALSE:
    zero = Minisat::mkLit(var.zero, false);
    one = Minisat::mkLit(var.one, true);
    break;
  case DrSign::TRUE:
    zero = Minisat::mkLit(var.zero, true);
    one = Minisat::mkLit(var.one, false);
    break;
  case DrSign::DC:
    break;
  }
  assert (Minisat::sign(one) || Minisat::sign(zero));
}
DrLit::DrLit(const DrVar& var, bool t_f_sign)
  : zero(Minisat::mkLit(var.zero, !t_f_sign)), // sign -> 1
    one(Minisat::mkLit(var.one, t_f_sign)) {   // sign -> 0
  assert (Minisat::sign(one) || Minisat::sign(zero));
}
DrLit::DrLit(Minisat::Lit std_lit) : DrLit(DrVar{Minisat::var(std_lit)}, Minisat::sign(std_lit)) {
  assert (std_lit.x > 1);
}
DrLit::DrLit(Minisat::Var std_var) {
  assert (std_var > 0);
  DrVar var_dr{std_var};
  // initialized with forbidden (1,1), but this is used for general clause constraints
  // over the zero/one literals
  this->zero = Minisat::mkLit(var_dr.zero, false);
  this->one = Minisat::mkLit(var_dr.one, false); 
}
DrLit::DrLit(Minisat::Var var, DrSign sign) : DrLit(DrVar{var}, sign) { }

bool DrLit::IsDontCare() const {
  assert (Minisat::sign(this->zero) || Minisat::sign(this->one)); // (1,1) forbidden
  if (Minisat::sign(this->one) && Minisat::sign(this->zero)) {
    return true; // (0,0) = X
  }
  return false;
}
Minisat::Lit DrLit::GetLitIfDef() const {
  // (1,1), shall not arrive here, has to be defined 0/1, (0,0) just picks 0
  if (!Minisat::sign(this->zero) && !Minisat::sign(this->one)) {
    throw runtime_error{"Tried to get a literal definition. But it is forbidden (1,1)."};
  }

  // invariant: zero holds the original variable index (that is what we want to return here)
  // FIXME: might be very unstable and error-prone to do it like that. I want to avoid another
  // field or so, though.
  return (~this->zero); // (zero = 1, one = 0) => ~lit, (zero = 0, one = 1) => lit
}
bool DrLit::IsInFinalConflict(Minisat::Solver& slv) const {
  if (slv.conflict.size() == 0) {
    throw logic_error{"Tried to check the final conflict of a solver. It is empty though."};
  }
  if (slv.conflict.has(this->one)) 
    return true;
  if (slv.conflict.has(this->zero)) 
    return true;
  return false;
}

DrVar::DrVar(Minisat::Var std_var)
  : zero(std_var),
    one(std_var + num_std_vars) {
  assert (std_var > 0);
}

void DrVar::AddOneOneExclusionCl(Minisat::Solver& slv) {
  Minisat::Lit zero_lit = Minisat::mkLit(this->zero, false);
  Minisat::Lit one_lit = Minisat::mkLit(this->one, false);
  slv.addClause(~zero_lit, ~one_lit);
}

void FreezeDrVar(Minisat::Var var, Minisat::SimpSolver& sslv) {
  if (var == 0) return; // no need to freeze constant 0/1
  DrVar dr_var{var};
  sslv.setFrozen(dr_var.zero, true);
  sslv.setFrozen(dr_var.one, true);
}
  
void AssumeDrLit(Minisat::Lit lit, MSLitVec& assumps) {
  DrLit dr_lit{DrVar{Minisat::var(lit)}, Minisat::sign(lit)};
  // either forcing 0 or 1
  if (!Minisat::sign(dr_lit.zero)) { // lit = 0
    assumps.push(dr_lit.zero);
    return;
  }
  if (!Minisat::sign(dr_lit.one)) // lit = 1
    assumps.push(dr_lit.one);
}
void AssumeDrLit(const DrLit& dr_lit, MSLitVec& assumps) {
  // can be (0,0) = X
  assert (Minisat::sign(dr_lit.one) || Minisat::sign(dr_lit.zero));
  assumps.push(dr_lit.zero);
  assumps.push(dr_lit.one);
}
void AssumeIndexedDrLit(Minisat::Lit lit, MSLitVec& assumps, int idx) {
  assert (idx < assumps.size());
  DrLit dr_lit{DrVar{Minisat::var(lit)}, Minisat::sign(lit)};
  // either forcing 0 or 1
  if (!Minisat::sign(dr_lit.zero)) { // lit = 0
    assumps[idx] =dr_lit.zero;
    return;
  }
  if (!Minisat::sign(dr_lit.one)) // lit = 1
     assumps[idx] = dr_lit.one;
}
// same logic as with assumptions
void AddDrLitToCl(Minisat::Lit lit, MSLitVec& cl) {
  if (Minisat::var(lit) == 0) { // constant, no dual rail encoding needed
    cl.push(lit);
    return;
  }
  AssumeDrLit(lit, cl);
}

void AddDrClause(Minisat::Lit lit, Minisat::Solver &slv) {
  if (Minisat::var(lit) == 0) { // constant, no dual rail encoding needed
    slv.addClause(lit);
    return;
  }
  DrLit dr_lit{DrVar{Minisat::var(lit)}, Minisat::sign(lit)};
  slv.addClause(!Minisat::sign(dr_lit.zero) ? dr_lit.zero : dr_lit.one);
}
void AddDrClause(Minisat::Lit lit1, Minisat::Lit lit2, Minisat::Solver &slv) {
  DrLit dr_lit1{DrVar{Minisat::var(lit1)}, Minisat::sign(lit1)};
  DrLit dr_lit2{DrVar{Minisat::var(lit2)}, Minisat::sign(lit2)};
  assert (Minisat::sign(dr_lit1.zero) != Minisat::sign(dr_lit1.one));
  assert (Minisat::sign(dr_lit2.zero) != Minisat::sign(dr_lit2.one));
  Minisat::Lit l1 = !Minisat::sign(dr_lit1.zero) ? dr_lit1.zero : dr_lit1.one;
  Minisat::Lit l2 = !Minisat::sign(dr_lit2.zero) ? dr_lit2.zero : dr_lit2.one;
  slv.addClause(l1, l2);
}
void AddDrClause(Minisat::Lit lit1, Minisat::Lit lit2, Minisat::Lit lit3, Minisat::Solver &slv) {
  DrLit dr_lit1{DrVar{Minisat::var(lit1)}, Minisat::sign(lit1)};
  DrLit dr_lit2{DrVar{Minisat::var(lit2)}, Minisat::sign(lit2)};
  DrLit dr_lit3{DrVar{Minisat::var(lit3)}, Minisat::sign(lit3)};
  Minisat::Lit l1 = !Minisat::sign(dr_lit1.zero) ? dr_lit1.zero : dr_lit1.one;
  Minisat::Lit l2 = !Minisat::sign(dr_lit2.zero) ? dr_lit2.zero : dr_lit2.one;
  Minisat::Lit l3 = !Minisat::sign(dr_lit3.zero) ? dr_lit3.zero : dr_lit3.one;
  slv.addClause(l1, l2, l3);
}
void AddDrClause(const Minisat::Clause& cl, Minisat::Solver& slv) {
  MSLitVec new_cl;
  new_cl.capacity(cl.size());
  for (auto i = 0; i < cl.size(); ++i) {
    Minisat::Lit lit = cl[i];
    DrLit dr_lit{DrVar{Minisat::var(lit)}, Minisat::sign(lit)};
    Minisat::Lit cl_lit = !Minisat::sign(dr_lit.zero) ? dr_lit.zero : dr_lit.one;
    new_cl.push(cl_lit);
  }
  slv.addClause_(new_cl);
}
void AddDrClause(const MSLitVec& cl, Minisat::Solver& slv) {
  MSLitVec new_cl;
  new_cl.capacity(cl.size());
  for (auto i = 0; i < cl.size(); ++i) {
    Minisat::Lit lit = cl[i];
    DrLit dr_lit{DrVar{Minisat::var(lit)}, Minisat::sign(lit)};
    Minisat::Lit cl_lit = !Minisat::sign(dr_lit.zero) ? dr_lit.zero : dr_lit.one;
    new_cl.push(cl_lit);
  }
  slv.addClause_(new_cl);
}
// takes a DrVar
DrLit getDrModel(const Var& var, const Minisat::Solver& slv) {
  DrVar var_dr{var.var()};
  Minisat::Var var_zero = var_dr.zero;
  Minisat::Var var_one = var_dr.one;
  bool zero_val = (slv.modelValue(var_zero) == Minisat::l_True);
  bool one_val = (slv.modelValue(var_one) == Minisat::l_True);
  
  DrSign sign;
  if (zero_val && !one_val) sign = DrSign::FALSE;
  else if (!zero_val && one_val) sign = DrSign::TRUE;
  else if (!zero_val && !one_val) sign = DrSign::DC;
  else throw runtime_error{"Forbidden (1,1) assignment detected."};
  
  return DrLit{var_dr, sign}; 
}