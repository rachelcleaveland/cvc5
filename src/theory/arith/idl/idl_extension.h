/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * IDL extension.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__IDL__IDL_EXTENSION_H
#define CVC5__THEORY__ARITH__IDL__IDL_EXTENSION_H

#include "context/cdlist.h"
#include "smt/env_obj.h"
#include "theory/skolem_lemma.h"
#include "theory/theory.h"
#include "theory/theory_model.h"

namespace cvc5 {
namespace theory {
namespace arith {

class TheoryArith;

namespace idl {

/**
 * Handles integer difference logic (IDL) constraints.
 */
class IdlExtension : protected EnvObj
{
 public:
  IdlExtension(Env& env, TheoryArith& parent);
  ~IdlExtension();

  /** Register a term that is in the formula */
  void preRegisterTerm(TNode);

  /** Set up the solving data structures */
  void presolve();

  void notifyFact(TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal); //TNode atom, bool polarity, TNode fact);

  /** Pre-processing of input atoms */
  Node ppRewrite(TNode atom, std::vector<SkolemLemma>& lems);

  /**
   * Provides access to the facts queue, primarily intended for theory
   * debugging purposes.
   *
   * @return the iterator to the beginning of the fact queue
   */
  Theory::assertions_iterator facts_begin() const;

  /**
   * Provides access to the facts queue, primarily intended for theory
   * debugging purposes.
   *
   * @return the iterator to the end of the fact queue
   */
  Theory::assertions_iterator facts_end() const;

  /** Check for conflicts in the current facts */
  void postCheck(Theory::Effort level);

  /** Get all information regarding the current model */
  bool collectModelInfo(TheoryModel* m, const std::set<Node>& termSet);

 private:
   enum validOptions : char 
  {
    INVALID = 0,
    POSITIVE = 1,
    NEGATIVE = 2
  };

 bool negativeCycleCheck(std::vector<bool> visited, size_t nextIdx, int level, std::vector<size_t> path);
 
  /** Process a new assertion */
  void processAssertion(TNode assertion);

  /** Construct the conflict clause */
  Node constructConflict();

  /** Return true iff the graph has a negative cycle */
  bool negativeCycle();

  /** Print the matrix */
  void printMatrix_cd(context::CDO<Rational>*** matrix,
                      context::CDO<validOptions>*** valid);
  
  typedef context::CDHashMap<TNode, size_t> TNodeToUnsignedCDMap;

  /** The owner of this extension */
  TheoryArith& d_parent;

  /** Map from variables to the first element of their list */
  TNodeToUnsignedCDMap d_varMap;

  /** Context-dependent vector of variables */
  context::CDList<TNode> d_varList;


  /** i,jth entry is true iff there is an edge from i to j. */
  std::vector<std::vector<bool>> d_valid;
  // Current : malloced array of CDOs
  context::CDO<validOptions>*** d_valid_cd;
  // std::vector<std::vector<context::CDO<bool>*>> d_valid_cd;

  //context::CDO<bool>* test;

  /** i,jth entry stores weight for edge from i to j. */
  std::vector<std::vector<Rational>> d_matrix;
  // Current : malloced array of CDOs
  context::CDO<Rational>*** d_matrix_cd;
  // std::vector<std::vector<context::CDO<Rational>*>> d_matrix_cd;
  
  context::CDO<Rational>** dist;

  /** Number of variables in the graph */
  size_t d_numVars;

  inline TNode get();
  context::CDO<bool> negative_cycle;
  context::CDList<size_t> conflictPath;

  context::CDO<std::tuple<size_t,size_t,Rational>>* conflictStart;
  //context::CDO<std::vector<size_t>>* conflictPath;

}; /* class IdlExtension */

}  // namespace idl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif
