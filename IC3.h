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

#ifndef IC3_h_INCLUDED
#define IC3_h_INCLUDED

#include "Model.h"

namespace IC3 {

  struct CertOpt {
    const char* proof_cert_path;
    const char* cex_path;
    CertOpt () : proof_cert_path(nullptr), cex_path(nullptr) {}
  };

  // A CubeSet is a set of ordered (by integer value) vectors of
  // Minisat::Lits.
  static bool _LitVecComp(const LitVec & v1, const LitVec & v2) {
    if (v1.size() < v2.size()) return true;
    if (v1.size() > v2.size()) return false;
    for (size_t i = 0; i < v1.size(); ++i) {
      if (v1[i] < v2[i]) return true;
      if (v2[i] < v1[i]) return false;
    }
    return false;
  }
  class LitVecComp {
  public:
    bool operator()(const LitVec & v1, const LitVec & v2) const {
      return _LitVecComp(v1, v2);
    }
  };
  typedef set<LitVec, LitVecComp> CubeSet;

  // For IC3's overall frame structure.
  struct Frame {
    size_t k;             // steps from initial state
    CubeSet borderCubes;  // additional cubes in this and previous frames
    Minisat::Solver * consecution;
  };

  bool check(Model & model,
             int verbose = 0,       // 0: silent, 1: stats, 2: informative
             bool basic = false,    // simple inductive generalization
             bool random = false,   // random runs for statistical profiling
             const CertOpt & certopt = CertOpt());

}

#endif
