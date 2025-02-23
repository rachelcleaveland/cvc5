/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Dejan Jovanovic, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SAT Solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__SAT_H
#define CVC5__PROP__SAT_H

// Just defining this for now, since there's no other SAT solver bindings.
// Optional blocks below will be unconditionally included
#define CVC5_USE_MINISAT

#include <unordered_set>

#include "context/cdqueue.h"
#include "expr/node.h"
#include "proof/trust_node.h"
#include "prop/registrar.h"
#include "prop/sat_solver_types.h"
#include "theory/theory.h"
#include "theory/theory_preprocessor.h"
#include "util/resource_manager.h"

namespace cvc5 {

class Env;
class TheoryEngine;

namespace decision {
class DecisionEngine;
}

namespace prop {

class PropEngine;
class CnfStream;
class SkolemDefManager;

/**
 * The proxy class that allows the SatSolver to communicate with the theories
 */
class TheoryProxy : public Registrar
{
 public:
  TheoryProxy(PropEngine* propEngine,
              TheoryEngine* theoryEngine,
              decision::DecisionEngine* decisionEngine,
              SkolemDefManager* skdm,
              Env& env);

  ~TheoryProxy();

  /** Finish initialize */
  void finishInit(CnfStream* cnfStream);

  /** Presolve, which calls presolve for the modules managed by this class */
  void presolve();

  /**
   * Notify a lemma or input assertion, possibly corresponding to a skolem
   * definition.
   */
  void notifyAssertion(Node lem,
                       TNode skolem = TNode::null(),
                       bool isLemma = false);

  void theoryCheck(theory::Theory::Effort effort);

  void explainPropagation(SatLiteral l, SatClause& explanation);

  void theoryPropagate(SatClause& output);

  void enqueueTheoryLiteral(const SatLiteral& l);

  SatLiteral getNextTheoryDecisionRequest();

  SatLiteral getNextDecisionEngineRequest(bool& stopSearch);

  bool theoryNeedCheck() const;

  /**
   * Notifies of a new variable at a decision level.
   */
  void variableNotify(SatVariable var);

  TNode getNode(SatLiteral lit);

  void notifyRestart();

  void spendResource(Resource r);

  bool isDecisionEngineDone();

  bool isDecisionRelevant(SatVariable var);

  SatValue getDecisionPolarity(SatVariable var);

  CnfStream* getCnfStream();

  /**
   * Call the preprocessor on node, return trust node corresponding to the
   * rewrite.
   */
  TrustNode preprocessLemma(TrustNode trn,
                            std::vector<theory::SkolemLemma>& newLemmas);
  /**
   * Call the preprocessor on node, return trust node corresponding to the
   * rewrite.
   */
  TrustNode preprocess(TNode node, std::vector<theory::SkolemLemma>& newLemmas);
  /**
   * Remove ITEs from the node.
   */
  TrustNode removeItes(TNode node, std::vector<theory::SkolemLemma>& newLemmas);
  /**
   * Get the skolems within node and their corresponding definitions, store
   * them in sks and skAsserts respectively. Note that this method does not
   * necessary include all of the skolems in skAsserts. In other words, it
   * collects from node only. To compute all skolems that node depends on
   * requires calling this method again on each lemma in skAsserts until a
   * fixed point is reached.
   */
  void getSkolems(TNode node,
                  std::vector<Node>& skAsserts,
                  std::vector<Node>& sks);
  /** Preregister term */
  void preRegister(Node n) override;

 private:
  /** The prop engine we are using. */
  PropEngine* d_propEngine;

  /** The CNF engine we are using. */
  CnfStream* d_cnfStream;

  /** The decision engine we are using. */
  decision::DecisionEngine* d_decisionEngine;

  /**
   * Whether the decision engine needs notification of active skolem
   * definitions, see DecisionEngine::needsActiveSkolemDefs.
   */
  bool d_dmNeedsActiveDefs;

  /** The theory engine we are using. */
  TheoryEngine* d_theoryEngine;

  /** Queue of asserted facts */
  context::CDQueue<TNode> d_queue;

  /**
   * Set of all lemmas that have been "shared" in the portfolio---i.e.,
   * all imported and exported lemmas.
   */
  std::unordered_set<Node> d_shared;

  /** The theory preprocessor */
  theory::TheoryPreprocessor d_tpp;

  /** The skolem definition manager */
  SkolemDefManager* d_skdm;

  /** Reference to the environment */
  Env& d_env;
}; /* class TheoryProxy */

}  // namespace prop

}  // namespace cvc5

#endif /* CVC5__PROP__SAT_H */
