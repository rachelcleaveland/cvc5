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
  //
  if (d_varMap.size() == 0) {
    unsigned size = d_varMap.size();
    TNode nullNode;
    d_varMap[nullNode] = size;
    d_varList.push_back(nullNode);
  }
  //
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


void IdlExtension::allocateEdgeWeights(size_t dimension) {
  edgeWeights = (context::CDHashMap<size_t,std::tuple<assertionOptions,Rational>>**)
	  malloc(sizeof(context::CDHashMap<size_t,std::tuple<assertionOptions,Rational>>*) * dimension);
  //edgeWeights2 = (context::CDHashMap<size_t,Rational>**)malloc(sizeof(context::CDHashMap<size_t,Rational>*) * dimension);
  for (size_t i = 0; i < dimension; ++i) {
    edgeWeights[i] = new(true) context::CDHashMap<size_t,std::tuple<assertionOptions,Rational>>(d_env.getContext());  
    //edgeWeights2[i] = new(true) context::CDHashMap<size_t,Rational>(d_env.getContext());  
  }
}

void IdlExtension::allocateMatrices(size_t dimension) {

  // Current : malloced array of CDOs
  dist = (context::CDO<Rational>**)malloc(sizeof(context::CDO<Rational>*) * dimension);

  for (size_t i = 0; i < dimension; ++i)
  {
    // Current : malloced array of pointers to CDOs
    dist[i] = new(true) context::CDO(d_env.getContext(), Rational(0));
  }

  /*
  edgeWeights2 = (context::CDHashMap<size_t,Rational>**)malloc(sizeof(context::CDHashMap<size_t,Rational>*) * dimension);
  for (size_t i = 0; i < dimension; ++i) {
    edgeWeights2[i] = new(true) context::CDHashMap<size_t,Rational>(d_env.getContext());  
  }
  */
}

void IdlExtension::presolve()
{
  d_numVars = d_varMap.size();
  Trace("theory::arith::idl")
      << "IdlExtension::preSolve(): d_numVars = " << d_numVars << std::endl;
 
  allocateEdgeWeights(d_numVars);
  allocateMatrices(d_numVars);

}

Node IdlExtension::ppRewrite(TNode atom, std::vector<SkolemLemma>& lems)
{
  Trace("theory::arith::idl")
      << "IdlExtension::ppRewrite(): processing " << atom << std::endl;
  NodeManager* nm = NodeManager::currentNM();

  if (  atom.getKind() == kind::EQUAL 
     || atom.getKind() == kind::LT
     || atom.getKind() == kind::LEQ
     || atom.getKind() == kind::GT
     || atom.getKind() == kind::GEQ) 
  {
     
    if (atom[0].getKind() == kind::CONST_RATIONAL) { 
      // Handle (op c (- x y)) cases ==> swap atoms, flip op

      kind::Kind_t atomKind = kind::EQUAL;
    
      switch (atom.getKind())
      {
        case kind::EQUAL: { atomKind = kind::EQUAL; break; }
        case kind::LT: { atomKind = kind::GT; break; }
        case kind::LEQ: { atomKind = kind::GEQ; break; }
        case kind::GT: { atomKind = kind::LT; break; }
        case kind::GEQ: { atomKind = kind::LEQ; break; }
        default: break;
      }

      return ppRewrite(nm->mkNode(atomKind, atom[1], atom[0]),lems);
    }

    if (atom[1].getKind() == kind::CONST_RATIONAL && atom[0].getKind() == kind::PLUS) {
      // Handle (op 
      Assert(atom[0][1].getKind() == kind::CONST_RATIONAL);

      Rational rightL = atom[0][1].getConst<Rational>();
      Rational rightR = atom[1].getConst<Rational>();

      return ppRewrite(nm->mkNode(atom.getKind(), atom[0][0], nm->mkConst(rightR - rightL)),lems);
      
    }

    if (atom[1].getKind() == kind::VARIABLE) { 
      // Handle (op x y) case ==> (op (- x y) 0)
      if (atom[0].getKind() == kind::VARIABLE) {
        return ppRewrite(nm->mkNode(atom.getKind(), nm->mkNode(kind::MINUS,atom[0],atom[1]),nm->mkConst(Rational(0))),lems);
      }
      // Handle (op (+ x c) y) ==> (op (- x y) -c)
      // Handle (op (- x c) y) ==> (op (- x y) c)
      Assert(atom[0].getKind() == kind::PLUS || atom[0].getKind() == kind::MINUS); // Handle (op (+ x c) y) case ==> (op (- x y) -c)
      Assert(atom[0][0].getKind() == kind::VARIABLE);
      Assert(atom[0][1].getKind() == kind::CONST_RATIONAL); 

      Rational right = atom[0][1].getConst<Rational>();
      if (atom[0].getKind() == kind::PLUS) {
	right = -right;
      }
      return ppRewrite(nm->mkNode(atom.getKind(), nm->mkNode(kind::MINUS, atom[0][0], atom[1]), nm->mkConst(right)),lems);
    }

    if (atom[1].getKind() == kind::PLUS || atom[1].getKind() == kind::MINUS) { 
      if (atom[0].getKind() == kind::VARIABLE) { 
	// Handle (op x (+ y c)) ==> (op (- x y) c)
	// Handle (op x (- y c)) ==> (op (- x y) -c)
	Rational right = atom[1][1].getConst<Rational>();
	if (atom[1].getKind() == kind::MINUS) {
	  right = -right;
	}
	return ppRewrite(nm->mkNode(atom.getKind(), nm->mkNode(kind::MINUS, atom[0], atom[1][0]), nm->mkConst(right)),lems);
      }
      Assert(atom[0].getKind() == kind::PLUS || atom[0].getKind() == kind::MINUS);
      Assert(atom[0][0].getKind() == kind::VARIABLE);
      Assert(atom[0][1].getKind() == kind::CONST_RATIONAL); 
      // Handle (op (+ x c) (+ y c2)) ==> (op (- x y) (-   c2    c   ))
      // Handle (op (+ x c) (- y c2)) ==> (op (- x y) (- (-c2)   c   ))
      // Handle (op (- x c) (+ y c2)) ==> (op (- x y) (-   c2  (-c)  ))
      // Handle (op (- x c) (- y c2)) ==> (op (- x y) (- (-c2) (-c)  ))
      
      Rational rightL = atom[0][1].getConst<Rational>();
      if (atom[0].getKind() == kind::MINUS) {
	rightL = -rightL;
      }
      Rational rightR = atom[1][1].getConst<Rational>();
      if (atom[1].getKind() == kind::MINUS) {
	rightR = -rightR;
      }

      return ppRewrite(nm->mkNode(atom.getKind(), nm->mkNode(kind::MINUS, atom[0][0], atom[1][0]), nm->mkConst(rightR-rightL)),lems);

    }
/*
    if ((atom[0].getKind() == kind::PLUS || atom[0].getKind() == kind::MINUS) && atom[0][1].getKind() == kind::CONST_RATIONAL) { // Handle (op (+ x c) c2) ==> (op x (- c2 c))
      Assert(atom[1].getKind() == kind::CONST_RATIONAL);
      
      Rational rightL = atom[0][1].getConst<Rational>();
      if (atom[0].getKind() == kind::MINUS) {
	rightL = -rightL;
      }
      Rational rightR = atom[1].getConst<Rational>();

      return ppRewrite(nm->mkNode(atom.getKind(), atom[0][0], nm->mkConst(rightR - rightL)),lems);

    }
*/
  }


  switch (atom.getKind())
  {
    case kind::EQUAL:
    {
      //if (atom[0].getKind() == kind::CONST_RATIONAL) {
	//return ppRewrite(nm->mkNode(kind::EQUAL, atom[1], atom[0]), lems);
      //}
      //std::cout << "in equals case " << std::endl;
      Node l_le_r = nm->mkNode(kind::LEQ, atom[0], atom[1]);
      Node negated_left;
      if (atom[0].getKind() == kind::VARIABLE) {
        negated_left = nm->mkNode(kind::UMINUS, atom[0]);
      } else {
        Assert(atom[0].getKind() == kind::MINUS);
        negated_left = nm->mkNode(kind::MINUS, atom[0][1], atom[0][0]);
      }
      //std::cout << "atom[1] " << atom[1] << std::endl;
      const Rational& right = atom[1].getConst<Rational>();
      //std::cout << "returned from right " << std::endl;
      Node negated_right = nm->mkConst(-right);
      Node r_le_l = nm->mkNode(kind::LEQ, negated_left, negated_right);
      //std::cout << "returned from equals case " << std::endl;
      return nm->mkNode(kind::AND, l_le_r, r_le_l);
    }

    // -------------------------------------------------------------------------
    // TODO: Handle these cases.
    // -------------------------------------------------------------------------
    case kind::LT:
    {
      const Rational& right = atom[1].getConst<Rational>();
      Node new_right = nm->mkConst(right - 1);
      return nm->mkNode(kind::LEQ, atom[0], new_right);
    }
    case kind::LEQ:
    {
      return atom;
    }
    case kind::GT:
    {
      Node negated_left;
      if (atom[0].getKind() == kind::VARIABLE) {
        negated_left = nm->mkNode(kind::UMINUS, atom[0]);
      } else {
        Assert(atom[0].getKind() == kind::MINUS);
        negated_left = nm->mkNode(kind::MINUS, atom[0][1], atom[0][0]);
      }

      const Rational& right = atom[1].getConst<Rational>();
      Node negated_right = nm->mkConst(-right - 1);
      return nm->mkNode(kind::LEQ, negated_left, negated_right);
    }
    case kind::GEQ:
    {  
      Node negated_left;
      if (atom[0].getKind() == kind::VARIABLE) {
        negated_left = nm->mkNode(kind::UMINUS, atom[0]);
      } else {
        Assert(atom[0].getKind() == kind::MINUS);
        negated_left = nm->mkNode(kind::MINUS, atom[0][1], atom[0][0]);
      }

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
 
  std::tuple<assertionOptions,Rational> tuple12 = (*edgeWeights[firstNode])[secondNode];
  Rational w = std::get<1>(tuple12);
  bool polarity = std::get<0>(tuple12) == PLUS;

  size_t firstNodeCon = firstNode;
  size_t secondNodeCon = secondNode;
  
  if (!polarity) {
    std::swap(firstNodeCon, secondNodeCon);
    w = -(w + Rational(1));    
  }
  
  NodeBuilder conjunction(kind::AND);

  Node constW = nm->mkConst(w);

  Node initialConflict;

  if (firstNodeCon == 0) {
    Assert(secondNodeCon != 0);
    initialConflict = nm->mkNode(kind::LEQ, nm->mkNode(kind::UMINUS, d_varList[secondNodeCon]), constW); 
  } else {
    if (secondNodeCon == 0) {
      initialConflict = nm->mkNode(kind::LEQ, d_varList[firstNodeCon], constW); 
    } else {
      initialConflict = nm->mkNode(kind::LEQ, nm->mkNode(kind::MINUS, d_varList[firstNodeCon], d_varList[secondNodeCon]), constW); 
    }
  }

  if (!polarity) {
    initialConflict = nm->mkNode(kind::NOT, initialConflict);
  }

  conjunction << initialConflict;

  for (size_t k = 0; k < conflictPath.size() - 1; k++) {
    size_t prevIdx = conflictPath[k];
    size_t currIdx = conflictPath[k+1];
    
    std::tuple<assertionOptions,Rational> tuplePC = (*edgeWeights[prevIdx])[currIdx];
    Rational weight = std::get<1>(tuplePC);
    polarity = std::get<0>(tuplePC) == PLUS;

    if (!polarity) {
      std::swap(prevIdx, currIdx);
      weight = -(weight + Rational(1));    
    }

    Node constWeight = nm->mkConst(weight);
    Node exprExt;

    if (prevIdx == 0) {
      Assert(currIdx != 0);
      exprExt = nm->mkNode(kind::LEQ, nm->mkNode(kind::UMINUS, d_varList[currIdx]), constWeight);
    } else {
      if (currIdx == 0) {
        exprExt = nm->mkNode(kind::LEQ, d_varList[prevIdx], constWeight); 
      } else {
        exprExt = nm->mkNode(kind::LEQ, nm->mkNode(kind::MINUS, d_varList[prevIdx], d_varList[currIdx]), constWeight); 
      }
    }

    if (!polarity) {
      exprExt = nm->mkNode(kind::NOT, exprExt);
    }

    conjunction << exprExt;
  }

  
  Node conflict; 
  if (conflictPath.size() == 1) {
    conflict = initialConflict;
  } else {
    conflict = conjunction;
  }

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
  
  NodeManager* nm = NodeManager::currentNM();
  for (size_t i = 1; i < d_numVars; i++)
  {
    // Assert that the variable's value is equal to its distance in the model
    m->assertEquality(d_varList[i], nm->mkConst(dist[i]->get()), true);
  }

  return true;
}

bool IdlExtension::negativeCycleCheck(std::vector<bool> visited, size_t nextIdx, int level, std::vector<size_t> *pathRef) {
  
  if (visited[nextIdx]) {
    if (!negative_cycle.get()) {
      negative_cycle.set(true);
      bool started = false;
      for (size_t k = 0; k < pathRef->size(); k++) {
        if (!started && (*pathRef)[k] == nextIdx) {
          started = true;
	}
	if (started) {
	  conflictPath.push_back((*pathRef)[k]);
	}
      }

    }
    return true;

  } else {

    visited[nextIdx] = true;
    for (size_t i = 0; i < d_numVars; i++) { //Update outgoing edges of each updated edge
      if (edgeWeights[nextIdx]->find(i) != edgeWeights[nextIdx]->end()) {
	std::tuple<assertionOptions,Rational> edgeW12Tuple = (*edgeWeights[nextIdx])[i];
        Rational edgeW12 = std::get<1>(edgeW12Tuple);
	
	if (dist[i]->get() > dist[nextIdx]->get() + edgeW12) {
	  dist[i]->set(dist[nextIdx]->get() + edgeW12);
	  
	  pathRef->push_back(nextIdx);
	  if (negativeCycleCheck(visited,i,level+1,pathRef)) {
	    return true;	   
	  } else {//Push each updated vertex to the queue
	    pathRef->pop_back();
	  }
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
  
  size_t index1;
  size_t index2;

  if (atom[0].getKind() == kind::VARIABLE) {
    
    TNode var1 = atom[0];
    
    index1 = d_varMap[var1];
    index2 = 0;

  } else if (atom[0].getKind() == kind::UMINUS && atom[0][0].getKind() == kind::VARIABLE) {
    TNode var2 = atom[0][0];

    index1 = 0;
    index2 = d_varMap[var2];

  } else {

    Assert(atom[0].getKind() == kind::MINUS);

    TNode var1 = atom[0][0];
    TNode var2 = atom[0][1];

    index1 = d_varMap[var1];
    index2 = d_varMap[var2];

  }
  
  Rational value = (atom[1].getKind() == kind::UMINUS)
                       ? -atom[1][0].getConst<Rational>()
                       : atom[1].getConst<Rational>();

  assertionOptions assertOp = PLUS;

  if (!polarity)
  {
    std::swap(index1,index2);
    value = -value - Rational(1);
    assertOp = MINUS;
  }

  std::tuple<assertionOptions,Rational> newEdge = std::make_tuple(assertOp,value);
  if (edgeWeights[index1]->find(index2) == edgeWeights[index1]->end()) {
    (*edgeWeights[index1])[index2] = newEdge;
  } else {
    std::tuple<assertionOptions,Rational> oldTupleValue = (*edgeWeights[index1])[index2];
    Rational oldValue = std::get<1>(oldTupleValue);
    if (oldValue > value) {
      (*edgeWeights[index1])[index2] = newEdge;
    } 
  }

  std::vector<bool> visited(d_numVars, false);
  
  if (edgeWeights[index1]->find(index2) != edgeWeights[index1]->end()) {
    std::tuple<assertionOptions,Rational> edgeW12Tuple = (*edgeWeights[index1])[index2];
    Rational edgeW12 = std::get<1>(edgeW12Tuple);
    if (dist[index2]->get() > dist[index1]->get() + edgeW12) {
      dist[index2]->set(dist[index1]->get() + edgeW12);
    }
  }

  if (!negative_cycle.get()) {
    std::vector<size_t> path = {};
    negativeCycleCheck(visited, index2, 0, &path);
  }

}


bool IdlExtension::negativeCycle()
{
  // --------------------------------------------------------------------------
  // TODO: write the code to detect a negative cycle.
  // --------------------------------------------------------------------------

  return negative_cycle.get();

}

/*
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
*/

void IdlExtension::notifyFact(TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal) {
  
  Assertion assertion = Assertion(fact, isPrereg);

  processAssertion(assertion.d_assertion);

}

IdlExtension::~IdlExtension() {
  for (size_t i = 0; i < d_numVars; ++i) {
    dist[i]->deleteSelf();
    edgeWeights[i]->~CDHashMap();
  }
  free(dist);
  free(edgeWeights);
}

}  // namespace idl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
