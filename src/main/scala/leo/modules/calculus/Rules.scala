package leo.modules.calculus

import leo.Out
import leo.datastructures.Literal.Side
import leo.datastructures._
import leo.modules.HOLSignature.{o, LitTrue}
import leo.modules.output.{SZS_EquiSatisfiable, SZS_Theorem}

////////////////////////////////////////////////////////////////
////////// Extensionality
////////////////////////////////////////////////////////////////

object FuncExt extends CalculusRule {
  val name = "func_ext"
  override val inferenceStatus = Some(SZS_EquiSatisfiable)

  def canApply(l: Literal): Boolean = l.equational && l.left.ty.isFunType
  type ExtLits = Literal
  type OtherLits = Literal
  def canApply(cl: Clause): (Boolean, Seq[ExtLits], Seq[OtherLits]) = {
    var can = false
    var extLits:Seq[Literal] = Seq()
    var otherLits: Seq[Literal] = Seq()
    val lits = cl.lits.iterator
    while (lits.hasNext) {
      val l = lits.next()
      if (canApply(l)) {
        extLits = extLits :+ l
        can = true
      } else {
        otherLits = otherLits :+ l
      }
    }
    (can, extLits, otherLits)
  }

  def apply(lit: Literal, vargen: leo.modules.calculus.FreshVarGen, initFV: Seq[(Int, Type)])(implicit sig: Signature): Literal = {
    assert(lit.left.ty.isFunType, "Trying to apply func ext on non fun-ty literal")
    assert(lit.equational, "Trying to apply func ext on non-eq literal")

    val funArgTys = lit.left.ty.funParamTypes
    if (lit.polarity) {
      // TODO: Maybe set implicitly quantified variables manually? Otherwise the whole terms is
      // traversed again and again
      val newVars = funArgTys.map {ty => vargen(ty)}
      Literal.mkOrdered(Term.mkTermApp(lit.left, newVars).betaNormalize, Term.mkTermApp(lit.right, newVars).betaNormalize, true)(sig)
    } else {
      val skTerms = funArgTys.map(leo.modules.calculus.skTerm(_, initFV, vargen.existingTyVars)(sig)) //initFV: We only use the
      // free vars that were existent at the very beginning, i.e. simulating
      // that we applies func_ext to all negative literals first
      // in order to minimize the FVs inside the sk-term
      Literal.mkOrdered(Term.mkTermApp(lit.left, skTerms).betaNormalize, Term.mkTermApp(lit.right, skTerms).betaNormalize, false)(sig)
    }
  }

  def apply(vargen: leo.modules.calculus.FreshVarGen, lits: Seq[Literal])(implicit sig: Signature): Seq[Literal] = {
    val initFV = vargen.existingVars
    lits.map(apply(_,vargen, initFV)(sig))
  }

}

object BoolExt extends CalculusRule {
  val name = "bool_ext"
  override val inferenceStatus = Some(SZS_Theorem)

  def canApply(l: Literal): Boolean = l.equational && l.left.ty == o
  type ExtLits = Seq[Literal]
  type OtherLits = Seq[Literal]

  def canApply(cl: Clause): (Boolean, ExtLits, OtherLits) = {
    var can = false
    var extLits:Seq[Literal] = Seq()
    var otherLits: Seq[Literal] = Seq()
    val lits = cl.lits.iterator
    while (lits.hasNext) {
      val l = lits.next()
      if (canApply(l)) {
        extLits = extLits :+ l
        can = true
      } else {
        otherLits = otherLits :+ l
      }
    }
    (can, extLits, otherLits)
  }

  def apply(extLits: ExtLits, otherLits: OtherLits): Set[Clause] = {
    var transformed = Set(otherLits)
    val extIt = extLits.iterator
    while (extIt.hasNext) {
      val extLit = extIt.next()
      val nu = apply(extLit)
      transformed = transformed.map(_ ++ nu._1) union transformed.map(_ ++ nu._2)
    }
    transformed.map(Clause.mkClause)
  }

  def apply(l: Literal): (ExtLits, ExtLits) = {
    assert(l.equational, "Trying to apply bool ext on non-eq literal")
    assert(l.left.ty == o && l.right.ty == o, "Trying to apply bool ext on non-bool literal")

    if (l.polarity) {
       (Seq(Literal.mkLit(l.left, false), Literal.mkLit(l.right, true)), Seq(Literal.mkLit(l.left, true), Literal.mkLit(l.right, false)))
    } else {
      (Seq(Literal.mkLit(l.left, false), Literal.mkLit(l.right, false)), Seq(Literal.mkLit(l.left, true), Literal.mkLit(l.right, true)))
    }
  }

}

////////////////////////////////////////////////////////////////
////////// pre-Unification
////////////////////////////////////////////////////////////////
protected[calculus] abstract class AnyUni extends CalculusRule {
  final override val inferenceStatus = Some(SZS_EquiSatisfiable)

  type UniLits = Seq[(Term, Term)]
  type OtherLits = Seq[Literal]
  type UniResult = (Clause, (Unification#TermSubst, Unification#TypeSubst))

  def canApply(l: Literal): Boolean

  final def canApply(cl: Clause): (Boolean, UniLits, OtherLits) = {
    var can = false
    var uniLits: UniLits = Seq()
    var otherLits: OtherLits = Seq()
    val lits = cl.lits.iterator
    while (lits.hasNext) {
      val l = lits.next()
      if (canApply(l)) {
        uniLits = uniLits :+ (l.left, l.right)
        can = true
      } else {
        otherLits = otherLits :+ l
      }
    }
    (can, uniLits, otherLits)
  }
}

object PreUni extends AnyUni {
  final val name = "pre_uni"

  final def canApply(l: Literal): Boolean = l.uni

  final def apply(vargen: FreshVarGen, uniLits: UniLits,
                  otherLits: OtherLits)(implicit sig: Signature): Iterator[UniResult] = {
    Out.debug(s"Unification on:\n\t${uniLits.map(eq => eq._1.pretty(sig) + " = " + eq._2.pretty(sig)).mkString("\n\t")}")
    val result = HuetsPreUnification.unifyAll(vargen, uniLits).iterator
    result.map {case (subst, flexflex) =>
      val newLiteralsFromFlexFlex = flexflex.map(eq => Literal.mkNeg(eq._1, eq._2))
      val updatedOtherLits = otherLits.map(_.substituteOrdered(subst._1, subst._2)(sig))
      val resultClause = Clause(updatedOtherLits ++ newLiteralsFromFlexFlex)
      (resultClause, subst)
    }
  }
}

object PatternUni extends AnyUni {
  final val name = "pattern_uni"

  final def canApply(l: Literal): Boolean =
    l.uni && PatternUnification.isPattern(l.left) && PatternUnification.isPattern(l.right)

  final def apply(vargen: FreshVarGen, uniLits: UniLits,
                  otherLits: OtherLits)(implicit sig: Signature): Option[UniResult] = {
    Out.debug(s"Pattern unification on:\n\t${uniLits.map(eq => eq._1.pretty(sig) + " = " + eq._2.pretty(sig)).mkString("\n\t")}")
    val result = PatternUnification.unifyAll(vargen, uniLits)
    if (result.isEmpty) None
    else {
      val subst = result.head._1
      val updatedOtherLits = otherLits.map(_.substituteOrdered(subst._1, subst._2)(sig))
      val resultClause = Clause(updatedOtherLits)
      Some((resultClause, subst))
    }
  }
}



////////////////////////////////////////////////////////////////
////////// Inferences
////////////////////////////////////////////////////////////////

object PrimSubst extends CalculusRule {
  val name = "prim_subst"
  override val inferenceStatus = Some(SZS_EquiSatisfiable)

  type FlexHeads = Set[Term]

  def canApply(cl: Clause): (Boolean, FlexHeads) = {
    var can = false
    var flexheads: FlexHeads = Set()
    val lits = cl.lits.iterator
    while (lits.hasNext) {
      val l = lits.next()
      if (l.flexHead) {
        flexheads = flexheads + l.left.headSymbol
        can = true
      }
    }
    Out.finest(s"flexHeads: ${flexheads.map(_.pretty).mkString(",")}")
    (can, flexheads)
  }

  def apply(cl: Clause, flexHeads: FlexHeads, hdSymbs: Set[Term])(implicit sig: Signature): Set[(Clause, Subst)] = hdSymbs.flatMap {hdSymb =>
    flexHeads.map {hd =>
//      println(s"${hd.pretty} - ${hd.fv.head._1}")
//      println(s"max fv: ${cl.maxImplicitlyBound}")
      val vargen = leo.modules.calculus.freshVarGen(cl)
      val binding = leo.modules.calculus.partialBinding(vargen,hd.ty, hdSymb)
      val subst = Subst.singleton(hd.fv.head._1, binding)
//      println(s"${subst.pretty}")
//      println(Literal(Term.mkBound(hd.fv.head._2, hd.fv.head._1), true).substitute(subst).pretty)
      (cl.substituteOrdered(subst)(sig),subst)
    }
  }
}


object OrderedEqFac extends CalculusRule {
  final val name = "eqfactor_ordered"
  final override val inferenceStatus = Some(SZS_Theorem)

  final def apply(cl: Clause, maxLitIndex: Int, maxLitSide: Side,
                  withLitIndex: Int, withLitSide: Side)(implicit sig: Signature): Clause = {
    assert(cl.lits.isDefinedAt(maxLitIndex))
    assert(cl.lits.isDefinedAt(withLitIndex))

    val maxLit = cl.lits(maxLitIndex)
    val withLit = cl.lits(withLitIndex)
    assert(maxLit.polarity || maxLit.flexHead)
    assert(withLit.polarity || withLit.flexHead)

    val (maxLitSide1, maxLitSide2) = Literal.getSidesOrdered(maxLit, maxLitSide)
    val (withLitSide1, withLitSide2) = Literal.getSidesOrdered(withLit, withLitSide)

    /* We cannot delete an element from the list, thats way we replace it by a trivially false literal,
    * i.e. it is lated eliminated using Simp. */
    val lits_without_maxLit = cl.lits.updated(maxLitIndex, Literal.mkLit(LitTrue(),false))
    val unification_task1: Literal = Literal.mkNegOrdered(maxLitSide1, withLitSide1)(sig)
    val unification_task2: Literal = Literal.mkNegOrdered(maxLitSide2, withLitSide2)(sig)

    val newlits = lits_without_maxLit :+ unification_task1 :+ unification_task2
    val newlitsSimp = Simp.shallowSimp(newlits)(sig)

    Clause(newlitsSimp)
  }


}

object OrderedParamod extends CalculusRule {
  final val name = "paramod_ordered"
  final override val inferenceStatus = Some(SZS_Theorem)

  /**
    *
    * @note Preconditions:
    * - withClause.lits(withIndex).polarity == true
    * - withSide == right => !withClause.lits(withIndex).oriented
    * - intoSide == right => !intoClause.lits(intoIndex).oriented
    * - if `t` is the `intoSide` of intoClause.lits(intoIndex), then
    *   u.fv = intoClause.implicitlyBound where `u` is a subterm of `t`
    * @param withClause clause that contains the literal used for rewriting
    * @param withIndex index of literal `s=t` in `withClause` that is used for rewriting
    * @param withSide `left` or `right`, depending on which side of `s=t` we search in `into`
    * @param intoClause clause that is rewritten
    * @param intoIndex index of literal `l=r` in `intoClause` that is rewritten
    * @param intoSide side of `l=r` that is rewritten
    * @param intoPosition position in `side(l=r)` that is rewritten
    */
  final def apply(withClause: Clause, withIndex: Int, withSide: Literal.Side,
            intoClause: Clause, intoIndex: Int, intoSide: Literal.Side, intoPosition: Position, intoSubterm: Term)(implicit sig: Signature): Clause = {
    assert(withClause.lits.isDefinedAt(withIndex))
    assert(intoClause.lits.isDefinedAt(intoIndex))
    assert(withClause.lits(withIndex).polarity)
    assert(!(withSide == Literal.rightSide) || !withClause.lits(withIndex).oriented)
    assert(!(intoSide == Literal.rightSide) || !intoClause.lits(intoIndex).oriented)

    val withLiteral = withClause.lits(withIndex)
    val (toFind, replaceBy) = if (withSide == Literal.leftSide) (withLiteral.left,withLiteral.right) else (withLiteral.right,withLiteral.left)

    Out.finest(s"toFind: ${toFind.pretty}")
    Out.finest(s"replaceBy: ${replaceBy.pretty}")

    /* We cannot delete an element from the list, thats way we replace it by a trivially false literal,
    * i.e. it is lated eliminated using Simp. */
    val withLits_without_withLiteral = withClause.lits.updated(withIndex, Literal.mkLit(LitTrue(),false))
    Out.finest(s"withLits_without_withLiteral: \n\t${withLits_without_withLiteral.map(_.pretty).mkString("\n\t")}")

    /* We shift all lits from intoClause to make the universally quantified variables distinct from those of withClause. */
    val withMaxTyVar = if (withClause.typeVars.isEmpty) 0 else withClause.typeVars.max
    val shiftedIntoLits = intoClause.lits.map(_.substitute(Subst.shift(withClause.maxImplicitlyBound), Subst.shift(withMaxTyVar))) // TOFIX reordering done
    Out.finest(s"IntoLits: ${intoClause.lits.map(_.pretty).mkString("\n\t")}")
    Out.finest(s"shiftedIntoLits: ${shiftedIntoLits.map(_.pretty).mkString("\n\t")}")

    // val intoLiteral = shiftedIntoLits(intoIndex) // FIXME Avoid reordering
    val intoLiteral = intoClause.lits(intoIndex)
    val (findWithin, otherSide) = if (intoSide == Literal.leftSide)
      (intoLiteral.left.substitute(Subst.shift(withClause.maxImplicitlyBound), Subst.shift(withMaxTyVar)),
        intoLiteral.right.substitute(Subst.shift(withClause.maxImplicitlyBound), Subst.shift(withMaxTyVar)))
    else
      (intoLiteral.right.substitute(Subst.shift(withClause.maxImplicitlyBound), Subst.shift(withMaxTyVar)),
        intoLiteral.left.substitute(Subst.shift(withClause.maxImplicitlyBound), Subst.shift(withMaxTyVar)))


    Out.finest(s"findWithin: ${findWithin.pretty}")
    Out.finest(s"otherSide: ${otherSide.pretty}")
    /* Replace subterm (and shift accordingly) */
    val rewrittenIntoLit = Literal.mkOrdered(findWithin.replaceAt(intoPosition,replaceBy.substitute(Subst.shift(intoPosition.abstractionCount))),otherSide,intoLiteral.polarity)(sig)
    /* Replace old literal in intoClause (at index intoIndex) by the new literal `rewrittenIntoLit` */
    val rewrittenIntoLits = shiftedIntoLits.updated(intoIndex, rewrittenIntoLit)
    /* unification literal between subterm of intoLiteral (in findWithin side) and right side of withLiteral. */
    Out.finest(s"withClause.maxImpBound: ${withClause.maxImplicitlyBound}")
    Out.finest(s"intoSubterm: ${intoSubterm.pretty}")
    Out.finest(s"shiftedIntoSubterm: ${intoSubterm.substitute(Subst.shift(withClause.maxImplicitlyBound)).pretty}")
    val unificationLit = Literal.mkNegOrdered(toFind, intoSubterm.substitute(Subst.shift(withClause.maxImplicitlyBound-intoPosition.abstractionCount), Subst.shift(withMaxTyVar)))(sig)

    Out.finest(s"unificationLit: ${unificationLit.pretty}")

    val newlits = withLits_without_withLiteral ++ rewrittenIntoLits :+ unificationLit
    val newlits_simp = Simp.shallowSimp(newlits)(sig)
    val resultingClause = Clause(newlits_simp)

    resultingClause
  }
}
