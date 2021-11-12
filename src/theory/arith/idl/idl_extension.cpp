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

#include "theory/arith/idl/idl_extension.h"

#include <iomanip>
#include <queue>
#include <set>

#include "expr/node_builder.h"
#include "theory/arith/theory_arith.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "util/rational.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace idl {

IdlExtension::IdlExtension(Env& env, TheoryArith& parent)
    : EnvObj(env),
      d_parent(parent),
      d_varMap(context()),
      d_varList(context()),
      d_numVars(0),
      negative_cycle(context(), false),
      conflictPath(context())
{
}


void printDist(size_t numVars, context::CDO<Rational>**  dists) {
  std::cout << "      ";
  for (size_t j = 0; j < numVars; j++) {
    std::cout << std::setw(6) << dists[j]->get();
  }
  std::cout << std::endl;
}

void IdlExtension::preRegisterTerm(TNode node)
{
  Assert(d_numVars == 0);
  if (node.isVar())
  {
    Trace("theory::arith::idl")
        << "IdlExtension::preRegisterTerm(): processing var " << node
        << std::endl;
    unsigned size = d_varMap.size();
    d_varMap[node] = size;
    d_varList.push_back(node);
  }
}

void IdlExtension::presolve()
{
  d_numVars = d_varMap.size();
  Trace("theory::arith::idl")
      << "IdlExtension::preSolve(): d_numVars = " << d_numVars << std::endl;

  // Initialize adjacency matrix.
  for (size_t i = 0; i < d_numVars; ++i)
  {
    d_matrix.emplace_back(d_numVars);
    d_valid.emplace_back(d_numVars, false);
  }

  // Current : malloced array of CDOs
  d_matrix_cd = (context::CDO<Rational>***)malloc(sizeof(context::CDO<Rational>**) * d_numVars);
  d_valid_cd = (context::CDO<validOptions>***)malloc(sizeof(context::CDO<validOptions>**) * d_numVars);
  dist = (context::CDO<Rational>**)malloc(sizeof(context::CDO<Rational>*) * d_numVars);
  conflictStart = new(true) context::CDO(d_env.getContext(), std::make_tuple((size_t)0,(size_t)0,Rational(0)));

  for (size_t i = 0; i < d_numVars; ++i)
  {
    // Current : malloced array of pointers to CDOs
    d_matrix_cd[i] = (context::CDO<Rational>**)malloc(sizeof(context::CDO<Rational>*) * d_numVars);
    d_valid_cd[i] = (context::CDO<validOptions>**)malloc(sizeof(context::CDO<validOptions>*) * d_numVars);
    dist[i] = new(true) context::CDO(d_env.getContext(), Rational(0));

  for (size_t j = 0; j < d_numVars; ++j) 
    {
      // Current : malloced array of pointers to CDOs
      d_valid_cd[i][j] = new(true) context::CDO(d_env.getContext(), INVALID);
      d_matrix_cd[i][j] = new(true) context::CDO(d_env.getContext(), Rational(0));

    }

  }

}

Node IdlExtension::ppRewrite(TNode atom, std::vector<SkolemLemma>& lems)
{
  Trace("theory::arith::idl")
      << "IdlExtension::ppRewrite(): processing " << atom << std::endl;
  NodeManager* nm = NodeManager::currentNM();

  switch (atom.getKind())
  {
    case kind::EQUAL:
    {
      Node l_le_r = nm->mkNode(kind::LEQ, atom[0], atom[1]);
      Assert(atom[0].getKind() == kind::MINUS);
      Node negated_left = nm->mkNode(kind::MINUS, atom[0][1], atom[0][0]);
      const Rational& right = atom[1].getConst<Rational>();
      Node negated_right = nm->mkConst(-right);
      Node r_le_l = nm->mkNode(kind::LEQ, negated_left, negated_right);
      return nm->mkNode(kind::AND, l_le_r, r_le_l);
    }

    // -------------------------------------------------------------------------
    // TODO: Handle these cases.
    // -------------------------------------------------------------------------
    case kind::LT:
    {
      Assert(atom[0].getKind() == kind::MINUS);
      const Rational& right = atom[1].getConst<Rational>();
      Node new_right = nm->mkConst(right - 1);
      return nm->mkNode(kind::LEQ, atom[0], new_right);
    }
    case kind::LEQ:
    {
      Assert(atom[0].getKind() == kind::MINUS);
      return atom;
    }
    case kind::GT:
    {
      Assert(atom[0].getKind() == kind::MINUS);
      Node negated_left = nm->mkNode(kind::MINUS, atom[0][1], atom[0][0]);
      const Rational& right = atom[1].getConst<Rational>();
      Node negated_right = nm->mkConst(-right - 1);
      return nm->mkNode(kind::LEQ, negated_left, negated_right);
    }
    case kind::GEQ:
    {
      Node negated_left = nm->mkNode(kind::MINUS, atom[0][1], atom[0][0]);
      const Rational& right = atom[1].getConst<Rational>();
      Node negated_right = nm->mkConst(-right);
      return nm->mkNode(kind::LEQ, negated_left, negated_right);
    }
      // -------------------------------------------------------------------------

    default: break;
  }
  return atom;
}

Theory::assertions_iterator IdlExtension::facts_begin() const
{
  return d_parent.facts_begin();
}

Theory::assertions_iterator IdlExtension::facts_end() const
{
  return d_parent.facts_end();
}

Node IdlExtension::constructConflict() {

  NodeManager* nm = NodeManager::currentNM();
  size_t firstNode = conflictPath[conflictPath.size()-1];
  size_t secondNode = conflictPath[0];
  Rational w = d_matrix_cd[firstNode][secondNode]->get();

  bool polarity = d_valid_cd[firstNode][secondNode]->get() == POSITIVE;

  size_t firstNodeCon = firstNode;
  size_t secondNodeCon = secondNode;
  
  if (!polarity) {
    std::swap(firstNodeCon, secondNodeCon);
    w = -(w + Rational(1));    
  }
  
  NodeBuilder conjunction(kind::AND);

  Node constW = nm->mkConst(w);
  Node initialConflict = nm->mkNode(kind::LEQ, nm->mkNode(kind::MINUS, d_varList[firstNodeCon], d_varList[secondNodeCon]), constW); //nm->mkConst(w));

  if (!polarity) {
    initialConflict = nm->mkNode(kind::NOT, initialConflict);
  }

  conjunction << initialConflict;

  for (size_t k = 0; k < conflictPath.size() - 1; k++) {
    size_t prevIdx = conflictPath[k];
    size_t currIdx = conflictPath[k+1];
    Rational weight = d_matrix_cd[prevIdx][currIdx]->get();

    polarity = d_valid_cd[prevIdx][currIdx]->get() == POSITIVE;

    if (!polarity) {
      std::swap(prevIdx, currIdx);
      weight = -(weight + Rational(1));    
    }

    Node constWeight = nm->mkConst(weight);

    Node exprExt = nm->mkNode(kind::LEQ, nm->mkNode(kind::MINUS, d_varList[prevIdx], d_varList[currIdx]), constWeight); //nm->mkConst(weight)); 
    
    if (!polarity) {
      exprExt = nm->mkNode(kind::NOT, exprExt);
    }

    conjunction << exprExt;
  }
  Node conflict = conjunction;

  return conflict;
}

void IdlExtension::postCheck(Theory::Effort level)
{
  if (!Theory::fullEffort(level))
  {
    return;
  }

  if (negativeCycle())
  { 

    Node conflict = constructConflict();

    // Send the conflict using the inference manager. Each conflict is assigned
    // an ID. Here, we use  ARITH_CONF_IDL_EXT, which indicates a generic
    // conflict detected by this extension
    d_parent.getInferenceManager().conflict(conflict,
                                            InferenceId::ARITH_CONF_IDL_EXT);
    return;
  }
}

bool IdlExtension::collectModelInfo(TheoryModel* m,
                                    const std::set<Node>& termSet)
{
  std::vector<Rational> distance(d_numVars, Rational(0));

  // ---------------------------------------------------------------------------
  // TODO: implement model generation by computing the single-source shortest
  // path from a node that has distance zero to all other nodes
  // ---------------------------------------------------------------------------
  for (size_t i = 0; i < d_numVars; i++) {
    for (size_t j = 0; j < d_numVars; j++) {
      if (d_valid_cd[i][j]->get()) {
	if (distance[j] > distance[i] + d_matrix_cd[i][j]->get()) {
	  distance[j] = distance[i] + d_matrix_cd[i][j]->get();
	}
      }
    }
  }

  NodeManager* nm = NodeManager::currentNM();
  for (size_t i = 0; i < d_numVars; i++)
  {
    // Assert that the variable's value is equal to its distance in the model
    m->assertEquality(d_varList[i], nm->mkConst(distance[i]), true);
  }

  return true;
}

bool IdlExtension::negativeCycleCheck(std::vector<bool> visited, size_t nextIdx, int level, std::vector<size_t> path) {
  //printDist(d_numVars, dist);
  if (visited[nextIdx]) {
    if (!negative_cycle.get()) {
      negative_cycle.set(true);
      bool started = false;
      for (size_t k = 0; k < path.size(); k++) {
        if (!started && path[k] == nextIdx) {
          started = true;
	}
	if (started) {
	  conflictPath.push_back(path[k]);
	}
      }

      size_t i = path[path.size()-1];
      conflictStart->set(std::make_tuple(i,nextIdx,d_matrix_cd[i][nextIdx]->get()));
    }
    return true;

  } else {

    visited[nextIdx] = true;
    for (size_t i = 0; i < d_numVars; i++) { //Update outgoing edges of each updated edge
      if (d_valid_cd[nextIdx][i]->get() != INVALID) {
	//std::cout << "checking edge " << nextIdx << " " << i << std::endl;
	//std::cout << "dist[" << i << "] = " << dist[i]->get() << " >? " << dist[nextIdx]->get() << " + " << d_matrix_cd[nextIdx][i]->get() << std::endl;
	if (dist[i]->get() > dist[nextIdx]->get() + d_matrix_cd[nextIdx][i]->get()) {
	  dist[i]->set(dist[nextIdx]->get() + d_matrix_cd[nextIdx][i]->get());
	  std::vector<size_t> newPath = path;
	  //std::vector<bool> visitedTemp = visited;
	  //std::cout << "adding " << i << std::endl;
	  newPath.push_back(nextIdx);
	  if (negativeCycleCheck(visited,i,level+1,newPath)) {
  	    //std::cout << "negativeCycleCheck on " << nextIdx << " " << i << std::endl;
	    return true;	   
	  } //Push each updated vertex to the queue
        }
      }
    }


  }
  return false;
}

void IdlExtension::processAssertion(TNode assertion)
{
  bool polarity = assertion.getKind() != kind::NOT;
  TNode atom = polarity ? assertion : assertion[0];
  Assert(atom.getKind() == kind::LEQ);
  Assert(atom[0].getKind() == kind::MINUS);
  TNode var1 = atom[0][0];
  TNode var2 = atom[0][1];

  Rational value = (atom[1].getKind() == kind::UMINUS)
                       ? -atom[1][0].getConst<Rational>()
                       : atom[1].getConst<Rational>();

  validOptions validity = POSITIVE;
  if (!polarity)
  {
    std::swap(var1, var2);
    value = -value - Rational(1);
    validity = NEGATIVE;
  }

  size_t index1 = d_varMap[var1];
  size_t index2 = d_varMap[var2];

  // Malloced array of CDOs 
  if ((d_valid_cd[index1][index2])->get()) {
    if (d_matrix_cd[index1][index2]->get() > value) {
      d_matrix_cd[index1][index2]->set(value);
      d_valid_cd[index1][index2]->set(validity);
    }
  } else {
    d_valid_cd[index1][index2]->set(validity);
    d_matrix_cd[index1][index2]->set(value);
  }

  std::vector<bool> visited(d_numVars, false);
 
  if (d_valid_cd[index1][index2]->get()) {
    if (dist[index2]->get() > dist[index1]->get() + d_matrix_cd[index1][index2]->get()) {
      dist[index2]->set(dist[index1]->get() + d_matrix_cd[index1][index2]->get());
    }
  }

  if (!negative_cycle.get()) {
    //std::cout << "negativeCycleCheck on " << index1 << " " << index2 << std::endl;
    negativeCycleCheck(visited, index2, 0, {});
  }

}


bool IdlExtension::negativeCycle()
{
  // --------------------------------------------------------------------------
  // TODO: write the code to detect a negative cycle.
  // --------------------------------------------------------------------------

  return negative_cycle.get();

}

void IdlExtension::printMatrix_cd(context::CDO<Rational>*** matrix,
                                  context::CDO<validOptions>*** valid)
{
  std::cout << "cd mat";
  for (size_t j = 0; j < d_numVars; ++j)
  {
    std::cout << std::setw(6) << d_varList[j];
  }
  std::cout << std::endl;
  for (size_t i = 0; i < d_numVars; ++i)
  {
    std::cout << std::setw(6) << d_varList[i];
    for (size_t j = 0; j < d_numVars; ++j)
    {
      if (valid[i][j]->get())
      {
        std::cout << std::setw(6) << matrix[i][j]->get();
      }
      else
      {
        std::cout << std::setw(6) << "oo";
      }
    }
    std::cout << std::endl;
  }
}

void IdlExtension::notifyFact(TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal) {
  
  Assertion assertion = Assertion(fact, isPrereg);

  processAssertion(assertion.d_assertion);

}

IdlExtension::~IdlExtension() {
  for (size_t i = 0; i < d_numVars; ++i) {
    for (size_t j = 0; j < d_numVars; ++j) {
      d_matrix_cd[i][j]->deleteSelf();
      d_valid_cd[i][j]->deleteSelf();
    }
    free(d_matrix_cd[i]);
    free(d_valid_cd[i]);
    dist[i]->deleteSelf();
  }
  free(d_matrix_cd);
  free(d_valid_cd);
  free(dist);
  conflictStart->deleteSelf();
}

}  // namespace idl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
