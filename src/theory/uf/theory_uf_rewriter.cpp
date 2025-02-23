/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory UF rewriter
 */

#include "theory/uf/theory_uf_rewriter.h"

#include "expr/node_algorithm.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"
#include "theory/uf/function_const.h"

namespace cvc5 {
namespace theory {
namespace uf {

TheoryUfRewriter::TheoryUfRewriter(bool isHigherOrder)
    : d_isHigherOrder(isHigherOrder)
{
}

RewriteResponse TheoryUfRewriter::postRewrite(TNode node)
{
  if (node.getKind() == kind::EQUAL)
  {
    if (node[0] == node[1])
    {
      return RewriteResponse(REWRITE_DONE,
                             NodeManager::currentNM()->mkConst(true));
    }
    else if (node[0].isConst() && node[1].isConst())
    {
      // uninterpreted constants are all distinct
      return RewriteResponse(REWRITE_DONE,
                             NodeManager::currentNM()->mkConst(false));
    }
    if (node[0] > node[1])
    {
      Node newNode =
          NodeManager::currentNM()->mkNode(node.getKind(), node[1], node[0]);
      return RewriteResponse(REWRITE_DONE, newNode);
    }
  }
  if (node.getKind() == kind::APPLY_UF)
  {
    if (node.getOperator().getKind() == kind::LAMBDA)
    {
      Trace("uf-ho-beta") << "uf-ho-beta : beta-reducing all args of : " << node
                          << "\n";
      TNode lambda = node.getOperator();
      Node ret;
      // build capture-avoiding substitution since in HOL shadowing may have
      // been introduced
      if (d_isHigherOrder)
      {
        std::vector<Node> vars;
        std::vector<Node> subs;
        for (const Node& v : lambda[0])
        {
          vars.push_back(v);
        }
        for (const Node& s : node)
        {
          subs.push_back(s);
        }
        if (Trace.isOn("uf-ho-beta"))
        {
          Trace("uf-ho-beta") << "uf-ho-beta: ..sub of " << subs.size()
                              << " vars into " << subs.size() << " terms :\n";
          for (unsigned i = 0, size = subs.size(); i < size; ++i)
          {
            Trace("uf-ho-beta")
                << "uf-ho-beta: .... " << vars[i] << " |-> " << subs[i] << "\n";
          }
        }
        ret = expr::substituteCaptureAvoiding(lambda[1], vars, subs);
        Trace("uf-ho-beta") << "uf-ho-beta : ..result : " << ret << "\n";
      }
      else
      {
        std::vector<TNode> vars(lambda[0].begin(), lambda[0].end());
        std::vector<TNode> subs(node.begin(), node.end());
        ret = lambda[1].substitute(
            vars.begin(), vars.end(), subs.begin(), subs.end());
      }
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }
    else if (!canUseAsApplyUfOperator(node.getOperator()))
    {
      return RewriteResponse(REWRITE_AGAIN_FULL, getHoApplyForApplyUf(node));
    }
  }
  else if (node.getKind() == kind::HO_APPLY)
  {
    if (node[0].getKind() == kind::LAMBDA)
    {
      // resolve one argument of the lambda
      Trace("uf-ho-beta") << "uf-ho-beta : beta-reducing one argument of : "
                          << node[0] << " with " << node[1] << "\n";

      // reconstruct the lambda first to avoid variable shadowing
      Node new_body = node[0][1];
      if (node[0][0].getNumChildren() > 1)
      {
        std::vector<Node> new_vars(node[0][0].begin() + 1, node[0][0].end());
        std::vector<Node> largs;
        largs.push_back(
            NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, new_vars));
        largs.push_back(new_body);
        new_body = NodeManager::currentNM()->mkNode(kind::LAMBDA, largs);
        Trace("uf-ho-beta")
            << "uf-ho-beta : ....new lambda : " << new_body << "\n";
      }

      // build capture-avoiding substitution since in HOL shadowing may have
      // been introduced
      if (d_isHigherOrder)
      {
        Node arg = Rewriter::rewrite(node[1]);
        Node var = node[0][0][0];
        new_body = expr::substituteCaptureAvoiding(new_body, var, arg);
      }
      else
      {
        TNode arg = Rewriter::rewrite(node[1]);
        TNode var = node[0][0][0];
        new_body = new_body.substitute(var, arg);
      }
      Trace("uf-ho-beta") << "uf-ho-beta : ..new body : " << new_body << "\n";
      return RewriteResponse(REWRITE_AGAIN_FULL, new_body);
    }
  }
  else if (node.getKind() == kind::LAMBDA)
  {
    Node ret = rewriteLambda(node);
    return RewriteResponse(REWRITE_DONE, ret);
  }
  return RewriteResponse(REWRITE_DONE, node);
}

RewriteResponse TheoryUfRewriter::preRewrite(TNode node)
{
  if (node.getKind() == kind::EQUAL)
  {
    if (node[0] == node[1])
    {
      return RewriteResponse(REWRITE_DONE,
                             NodeManager::currentNM()->mkConst(true));
    }
    else if (node[0].isConst() && node[1].isConst())
    {
      // uninterpreted constants are all distinct
      return RewriteResponse(REWRITE_DONE,
                             NodeManager::currentNM()->mkConst(false));
    }
  }
  return RewriteResponse(REWRITE_DONE, node);
}

Node TheoryUfRewriter::getHoApplyForApplyUf(TNode n)
{
  Assert(n.getKind() == kind::APPLY_UF);
  Node curr = n.getOperator();
  for (unsigned i = 0; i < n.getNumChildren(); i++)
  {
    curr = NodeManager::currentNM()->mkNode(kind::HO_APPLY, curr, n[i]);
  }
  return curr;
}
Node TheoryUfRewriter::getApplyUfForHoApply(TNode n)
{
  Assert(n.getType().getNumChildren() == 2);
  std::vector<TNode> children;
  TNode curr = decomposeHoApply(n, children, true);
  // if operator is standard
  if (canUseAsApplyUfOperator(curr))
  {
    return NodeManager::currentNM()->mkNode(kind::APPLY_UF, children);
  }
  // cannot construct APPLY_UF if operator is partially applied or is not
  // standard
  return Node::null();
}
Node TheoryUfRewriter::decomposeHoApply(TNode n,
                                        std::vector<TNode>& args,
                                        bool opInArgs)
{
  TNode curr = n;
  while (curr.getKind() == kind::HO_APPLY)
  {
    args.push_back(curr[1]);
    curr = curr[0];
  }
  if (opInArgs)
  {
    args.push_back(curr);
  }
  std::reverse(args.begin(), args.end());
  return curr;
}
bool TheoryUfRewriter::canUseAsApplyUfOperator(TNode n) { return n.isVar(); }

Node TheoryUfRewriter::rewriteLambda(Node node)
{
  Assert(node.getKind() == kind::LAMBDA);
  // The following code ensures that if node is equivalent to a constant
  // lambda, then we return the canonical representation for the lambda, which
  // in turn ensures that two constant lambdas are equivalent if and only
  // if they are the same node.
  // We canonicalize lambdas by turning them into array constants, applying
  // normalization on array constants, and then converting the array constant
  // back to a lambda.
  Trace("builtin-rewrite") << "Rewriting lambda " << node << "..." << std::endl;
  Node anode = FunctionConst::getArrayRepresentationForLambda(node);
  // Only rewrite constant array nodes, since these are the only cases
  // where we require canonicalization of lambdas. Moreover, applying the
  // below code is not correct if the arguments to the lambda occur
  // in return values. For example, lambda x. ite( x=1, f(x), c ) would
  // be converted to (store (storeall ... c) 1 f(x)), and then converted
  // to lambda y. ite( y=1, f(x), c), losing the relation between x and y.
  if (!anode.isNull() && anode.isConst())
  {
    Assert(anode.getType().isArray());
    // must get the standard bound variable list
    Node varList = NodeManager::currentNM()->getBoundVarListForFunctionType(
        node.getType());
    Node retNode =
        FunctionConst::getLambdaForArrayRepresentation(anode, varList);
    if (!retNode.isNull() && retNode != node)
    {
      Trace("builtin-rewrite") << "Rewrote lambda : " << std::endl;
      Trace("builtin-rewrite") << "     input  : " << node << std::endl;
      Trace("builtin-rewrite")
          << "     output : " << retNode << ", constant = " << retNode.isConst()
          << std::endl;
      Trace("builtin-rewrite")
          << "  array rep : " << anode << ", constant = " << anode.isConst()
          << std::endl;
      Assert(anode.isConst() == retNode.isConst());
      Assert(retNode.getType() == node.getType());
      Assert(expr::hasFreeVar(node) == expr::hasFreeVar(retNode));
      return retNode;
    }
  }
  else
  {
    Trace("builtin-rewrite-debug")
        << "...failed to get array representation." << std::endl;
  }
  return node;
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5
