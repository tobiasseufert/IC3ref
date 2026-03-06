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

#include <iostream>
#include "Certificate.h"

void Certificate::BuildCertifaiger() {
  for (size_t i = invar_idx; i < frames.size(); ++i) {
    const IC3::Frame& fr = frames.at(i);
    for (const auto& cube : fr.borderCubes) {
      AigerAndsOfCube(cube);
    }
  }
  OrOfAllBlockedCubes();
  FinalBigOr();
}

void Certificate::AigerAndsOfCube(const LitVec& cube) {
  Minisat::Lit curr = cube[0];
  for (size_t i = 1; i < cube.size(); ++i) {
    curr = NewAnd(curr, cube[i]);
  }
  RegisterAndOp(curr);
}

void Certificate::OrOfAllBlockedCubes() {
  if (cube_ands.empty()) {
    cerr << "Certificate creation: trivial, no learned clauses present." << endl;
    return;
  }
  Minisat::Lit curr = cube_ands[0];
  for (size_t i = 1; i < cube_ands.size(); ++i) {
    curr = NewOr(curr, cube_ands[i]);
  }
  RegisterOrOfBlockeds(curr);
}

void Certificate::FinalBigOr() {
  if (!cube_ands.empty()) {
    if (blocked_cubes_or == Minisat::Lit{0})
      throw runtime_error("Certificate production failed. No negation of found inductive invariant produced.");
    CertOut(NewOr(blocked_cubes_or, model.error()));
  } else {
    TrivialCertOut();
  }
}

void Certificate::PrintCertificate() {
  const char* errmsg = aiger_check(aig);
  if (errmsg) {
    throw runtime_error(string("Syntax error in certificate creation, aborted due to AIGER error message: ") + errmsg);
  } else {
    int ret = aiger_open_and_write_to_file(aig, cert_path);
    if(!ret) {
      throw runtime_error("I/O error in certificate creation, aborted.");
    }
  }
}