/*********************************************************************
 Copyright (c) 2025, Tobias Seufert

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

#ifndef CERTIFICATE_H_INCLUDED
#define CERTIFICATE_H_INCLUDED

#include "IC3.h"

class Certificate {
 public:
  Certificate(Model& m_,
              const std::vector<IC3::Frame>& frames_,
              size_t invar_idx_,
              const char* cert_path_)
      : model(m_),
        frames(frames_),
        invar_idx(invar_idx_),
        curr_max_var(model.getAigMaxVar()),
        aig(aiger_init()),
        init(m_.getInitLits()),
        blocked_cubes_or(Minisat::Lit{0}),
        cert_path(cert_path_) {
    for (VarVec::const_iterator i = model.beginInputs(); i != model.endInputs(); ++i)
      AddInputToAiger(i);
    for (VarVec::const_iterator i = model.beginLatches(); i != model.endLatches(); ++i)
      AddLatchToAiger(i);
    for (AigVec::const_iterator a = model.beginAnds(); a != model.endAnds(); ++a)
      AddAndToAiger(a);
    BuildCertifaiger();
  }

  ~Certificate() {
    if (aig) aiger_reset(aig);
  }

  void PrintCertificate();

 private:
  Model& model;
  const std::vector<IC3::Frame>& frames;
  size_t invar_idx;
  unsigned curr_max_var;
  aiger* aig;
  LitVec cube_ands;
  LitVec init;
  Minisat::Lit blocked_cubes_or;
  const char* cert_path;

  void BuildCertifaiger();
  IC3::CubeSet GetEquivalenceCandidatesForAig();
  void AigerAndsOfCube(const LitVec& cube);
  void FinalBigOr();
  void OrOfNegInit();
  void OrOfAllBlockedCubes();

  inline void AddInputToAiger(VarVec::const_iterator i) {
    aiger_add_input(aig, Minisat::toInt(i->lit(false)), i->name().c_str());
  }

  inline void AddLatchToAiger(VarVec::const_iterator i) {
    aiger_add_latch(aig,
                    Minisat::toInt(i->lit(false)),
                    Minisat::toInt(model.nextStateFn(*i)),
                    i->name().c_str());
    // FIXME: tedious reverse engineering of resets (because original aiger is reset already)             
    unsigned reset = static_cast<unsigned>(
                        std::binary_search(model.getInitLits().begin(),
                                     model.getInitLits().end(),
                                     i->lit(false)));
    if (!reset) { 
      reset = static_cast<unsigned>(
                !std::binary_search(model.getInitLits().begin(),
                                     model.getInitLits().end(),
                                     i->lit(true)));
      if (reset) {
        // DC
        reset = Minisat::toInt(i->lit(false));
      }    
    }                                 
    aiger_add_reset(aig,
                    Minisat::toInt(i->lit(false)),
                    reset);
  }

  inline void AddAndToAiger(AigVec::const_iterator a) {
    aiger_add_and(aig,
                  Minisat::toInt(a->lhs),
                  Minisat::toInt(a->rhs0),
                  Minisat::toInt(a->rhs1));
  }

  inline void RegisterAndOp(Minisat::Lit lhs) { cube_ands.push_back(lhs); }


  inline void RegisterOrOfBlockeds(Minisat::Lit or_lit) {
    blocked_cubes_or = or_lit;
  }

  inline Minisat::Lit NewAnd(Minisat::Lit rhs0_, Minisat::Lit rhs1_) {
    ++curr_max_var;
    unsigned lhs = aiger_var2lit(curr_max_var);
    aiger_add_and(aig, lhs, Minisat::toInt(rhs0_), Minisat::toInt(rhs1_));
    assert (lhs <= INT_MAX);
    return Minisat::toLit(static_cast<int>(lhs));
  }

  inline Minisat::Lit NewOr(Minisat::Lit rhs0_, Minisat::Lit rhs1_) {
    ++curr_max_var;
    unsigned lhs = aiger_var2lit(curr_max_var);
    // a | b = ~ (~a & ~b)
    aiger_add_and(aig, lhs, Minisat::toInt(~rhs0_), Minisat::toInt(~rhs1_));
    assert (lhs <= INT_MAX);
    return ~Minisat::toLit(static_cast<int>(lhs));
  }

  inline void CertOut(Minisat::Lit out) {
    int lit = Minisat::toInt(out);
    assert (lit > 0);
    unsigned out_aiger = static_cast<unsigned>(lit);
    aiger_add_output(aig, out_aiger, "O_cert");
  }

  inline void TrivialCertOut() {
    unsigned out = Minisat::toInt(model.error());
    aiger_add_output(aig, out, "one_inductive");
  }
};

#endif  // CERTIFICATE_H_INCLUDED