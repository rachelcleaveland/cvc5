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
      negative_cycle(context(), false)
{
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
  d_valid_cd = (context::CDO<bool>***)malloc(sizeof(context::CDO<bool>**) * d_numVars);
  dist = (context::CDO<Rational>**)malloc(sizeof(context::CDO<Rational>*) * d_numVars);

  for (size_t i = 0; i < d_numVars; ++i)
  {
    // Current : malloced array of pointers to CDOs
    d_matrix_cd[i] = (context::CDO<Rational>**)malloc(sizeof(context::CDO<Rational>*) * d_numVars);
    d_valid_cd[i] = (context::CDO<bool>**)malloc(sizeof(context::CDO<bool>*) * d_numVars);
    dist[i] = new(true) context::CDO(d_env.getContext(), Rational(0));

  for (size_t j = 0; j < d_numVars; ++j) 
    {
      // Current : malloced array of pointers to CDOs
      d_valid_cd[i][j] = new(true) context::CDO(d_env.getContext(), false);
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

void IdlExtension::postCheck(Theory::Effort level)
{
  if (!Theory::fullEffort(level))
  {
    return;
  }

  if (negativeCycle())
  {
    // Return a conflict that includes all the literals that have been asserted
    // to this theory solver. A better implementation would only include the
    // literals involved in the conflict here.
    NodeBuilder conjunction(kind::AND);
    for (Theory::assertions_iterator i = facts_begin(); i != facts_end(); ++i)
    {
      conjunction << (*i).d_assertion;
    }
    Node conflict = conjunction;
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
/*
  for (size_t i = 0; i < d_numVars; i++) {
    for (size_t j = 0; j < d_numVars; j++) {
      if (d_valid[i][j]) {
	if (distance[j] > distance[i] + d_matrix[i][j]) {
	  distance[j] = distance[i] + d_matrix[i][j];
	}
      }
    }
  }
*/
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

  if (!polarity)
  {
    std::swap(var1, var2);
    value = -value - Rational(1);
  }

  size_t index1 = d_varMap[var1];
  size_t index2 = d_varMap[var2];

  // Malloced array of CDOs 
  if ((d_valid_cd[index1][index2])->get()) {
    if (d_matrix_cd[index1][index2]->get() > value) {
      d_matrix_cd[index1][index2]->set(value);
    }
  } else {
    d_valid_cd[index1][index2]->set(true);
    d_matrix_cd[index1][index2]->set(value);
  }


  //printMatrix_cd(d_matrix_cd, d_valid_cd);
  //new_edges_queue.push(std::make_tuple(index1,index2));

  /*
  if ((d_valid_cd_vec[index1][index2])->get()) {
    if (d_matrix_cd_vec[index1][index2]->get() > value) {
      d_matrix_cd_vec[index1][index2]->set(value);
    }
  } else {
    d_valid_cd_vec[index1][index2]->set(true);
    d_matrix_cd_vec[index1][index2]->set(value);
  }
  */
  std::queue<size_t> toVisit;
  std::vector<bool> visited(d_numVars, false);

  /* New way of detecting negative cycles */
  if (dist[index2]->get() > dist[index1]->get() + d_matrix_cd[index1][index2]->get()) {
    dist[index2]->set(dist[index1]->get() + d_matrix_cd[index1][index2]->get());
    toVisit.push(index2);
  } //dist[index2] only reduces here

  while (!toVisit.empty()) {
    size_t nextIdx = toVisit.front();
    toVisit.pop();

    if (visited[nextIdx]) {
      for (size_t i = 0; i < d_numVars; i++) {
	if (d_valid_cd[nextIdx][i]->get()) {
	  if (dist[i]->get() > dist[nextIdx]->get() + d_matrix_cd[nextIdx][i]->get()) {
	    negative_cycle.set(true);
	  }
	}
      }

    } else {

      for (size_t i = 0; i < d_numVars; i++) { //Update outgoing edges of each updated edge
	if (d_valid_cd[nextIdx][i]->get()) {
	  if (dist[i]->get() > dist[nextIdx]->get() + d_matrix_cd[nextIdx][i]->get()) {
	    dist[i]->set(dist[nextIdx]->get() + d_matrix_cd[nextIdx][i]->get());
	    toVisit.push(i); //Push each updated vertex to the queue
	  }
	}
      }

      visited[nextIdx] = true;

    }
  }

  /*
  if (!negative_cycle.get()) {
    for (size_t j = 0; j < d_numVars; j++) {
      if (d_valid_cd[index2][j]->get()) {
        if (dist[j]->get() > dist[index2]->get() + d_matrix_cd[index2][j]->get()) {
          negative_cycle.set(true);
        }
      }
    }
  }
  */

  //printMatrix_cd(d_matrix_cd, d_valid_cd);
}

void printDist(size_t numVars, const std::vector<Rational>& dists) {
  std::cout << "      ";
  for (size_t j = 0; j < numVars; j++) {
    std::cout << std::setw(6) << dists[j];
  }
  std::cout << std::endl;
}


bool IdlExtension::negativeCycle()
{
  // --------------------------------------------------------------------------
  // TODO: write the code to detect a negative cycle.
  // --------------------------------------------------------------------------

  //printMatrix_cd(d_matrix_cd, d_valid_cd);
  //std::cout << "negativeCycle" << std::endl;

  /*
  //Update distance vector, CD matrix
  std::vector<Rational> dist(d_numVars,0);
  for (size_t k = 0; k < d_numVars; k++) {
    for (size_t i = 0; i < d_numVars; i++) {
      for (size_t j = 0; j < d_numVars; j++) {
        if (d_valid_cd[i][j]->get()) {
	  if (dist[j] > dist[i] + d_matrix_cd[i][j]->get()) {
	    dist[j] = dist[i] + d_matrix_cd[i][j]->get();
	  }
        }
      }
    }
  }
  */
  

/*  Update distance vector, queue of indices
  std::vector<size_t> modified_dists;

  while (!new_edges_queue.empty()) {
    std::tuple<size_t, size_t> ij = new_edges_queue.front();
    new_edges_queue.pop();

    size_t i = std::get<0>(ij);
    size_t j = std::get<1>(ij);
    if (d_valid_cd[i][j]->get()) {
      if (dist[j] > dist[i] + d_matrix_cd[i][j]->get()) {
        modified_dists.push_back(j);
        dist[j] = dist[i] + d_matrix_cd[i][j]->get();
      }
    }
 }
*/
 
/* Update negative cycle, only modified indices
  size_t mod_size = modified_dists.size();

  for (size_t i = 0; i < mod_size; i++) {  
    for (size_t j = 0; j < mod_size; j++) {

      size_t modi = modified_dists[i];
      size_t modj = modified_dists[j];

      if (d_valid_cd[modi][modj]->get()) {
	if (dist[modj] > dist[modi] + d_matrix_cd[modi][modj]->get()) {
	  return true;
	}
      }
     
    }
  }
  */

  /* 
  // Return negative cycle, CD matrix, CD dist
  for (size_t i = 0; i < d_numVars; i++) {
    for (size_t j = 0; j < d_numVars; j++) {
      if (d_valid_cd[i][j]->get()) {
	if (dist[j]->get() > dist[i]->get() + d_matrix_cd[i][j]->get()) {
	  return true;
	}
      }
    }
  }
  */

  /* 
  // Return negative cycle, CD matrix, non-CD dist
  for (size_t i = 0; i < d_numVars; i++) {
    for (size_t j = 0; j < d_numVars; j++) {
      if (d_valid_cd[i][j]->get()) {
	if (dist[j] > dist[i] + d_matrix_cd[i][j]->get()) {
	  return true;
	}
      }
    }
  }
  */

  return negative_cycle.get();

  //return false;
}

void IdlExtension::printMatrix(const std::vector<std::vector<Rational>>& matrix,
                               const std::vector<std::vector<bool>>& valid)
{
  std::cout << "      ";
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
      if (valid[i][j])
      {
        std::cout << std::setw(6) << matrix[i][j];
      }
      else
      {
        std::cout << std::setw(6) << "oo";
      }
    }
    std::cout << std::endl;
  }
}

void IdlExtension::printMatrix_cd(context::CDO<Rational>*** matrix,
                                  context::CDO<bool>*** valid)
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

void IdlExtension::printMatrix_cd_vec(std::vector<std::vector<context::CDO<Rational>*>> matrix,
                                      std::vector<std::vector<context::CDO<bool>*>> valid)
{
  std::cout << "cd vec";
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
}

}  // namespace idl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
