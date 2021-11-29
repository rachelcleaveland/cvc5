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

  void allocateMatrices(size_t dimension);
  void allocateEdgeWeights(size_t dimension);

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
 
  enum assertionOptions : char
  {
    PLUS = 0,
    MINUS = 1
  };

  bool negativeCycleCheck(std::vector<bool> visited, size_t nextIdx, int level, std::vector<size_t> *path);
 
  /** Process a new assertion */
  void processAssertion(TNode assertion);

  /** Construct the conflict clause */
  Node constructConflict();

  /** Return true iff the graph has a negative cycle */
  bool negativeCycle();

  /** Print the matrix */
  /*void printMatrix_cd(context::CDO<Rational>*** matrix,
                      context::CDO<validOptions>*** valid);
  */

  typedef context::CDHashMap<TNode, size_t> TNodeToUnsignedCDMap;

  /** The owner of this extension */
  TheoryArith& d_parent;

  /** Map from variables to the first element of their list */
  TNodeToUnsignedCDMap d_varMap;

  /** Context-dependent vector of variables */
  context::CDList<TNode> d_varList;

  /* Array of CDOs representing Bellman-Ford distance to each vertex */
  context::CDO<Rational>** dist;

  /** Number of variables in the graph */
  size_t d_numVars;

  context::CDO<bool> negative_cycle;
  
  /* List of node indicies in negative cycle */
  context::CDList<size_t> conflictPath;

  /* 
   * Adjacency matrix: edge list representation 
   *   each vertex has a hash map containing its outgoing edges 
   */
  context::CDHashMap<size_t,std::tuple<assertionOptions,Rational>>** edgeWeights; 

}; /* class IdlExtension */

}  // namespace idl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif
