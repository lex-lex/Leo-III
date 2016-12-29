package leo.modules.calculus

import leo.datastructures.{Subst, Term}
import scala.annotation.tailrec

/**
  * General trait for anti-unification algorithms. For general higher order terms
  * there exists no unique lgg/msg.
  */
trait AntiUnification {
  type TermSubst = Subst; type TypeSubst = Subst
  type FullSubst = (TermSubst, TypeSubst)
  type Result = (Term, FullSubst, FullSubst)

  /** Given two terms s and t, this method gives triples (r, σ, ϱ) such that
    * (1) r = sσ
    * (2) r = tϱ
    * (3) r is a least general (most specific) generalization of s and t. */
  def antiUnify(vargen: FreshVarGen, s: Term, t: Term): Iterable[Result]
  // TODO Does Iterable[.] make sense here? For general HO terms there could a series of those results
}

/**
  * Higher-Order Pattern Anti-Unification implementation of
  * Baumgartner et al. "Higher-Order Pattern Anti-Unification in Linear Time"
  * (J. Automated Reasoning, DOI 10.1007/s10817-016-9383-3).
  *
  * @author Alexander Steen <a.steen@fu-berlin.de>
  * @since 21.12.2016
  */
object PatternAntiUnification extends AntiUnification {
  import leo.datastructures.Type

  /** Given two terms s and t, this method gives a triple (r, σ, ϱ) such that
    * (1) r = sσ
    * (2) r = tϱ
    * (3) r is a least general (most specific) generalization of s and t
    * (4) r is a higher-order pattern. */
  final def antiUnify(vargen: FreshVarGen, s: Term, t: Term): Iterable[Result] = {
    Iterable(antiUnify0(vargen, s.etaExpand, t.etaExpand))
  }

  final def antiUnify0(vargen: FreshVarGen, s: Term, t: Term): Result = {
    solve(vargen, s, t)
  }

  type AbstractionVar = Term
  type Depth = Seq[Term]
  type Eq = (AbstractionVar, Depth, Term, Term)
  type Unsolved = Seq[Eq]
  type Solved = Unsolved
  private final def solve(vargen: FreshVarGen,
                          s: Term, t: Term): Result = {
    leo.Out.debug(s"Solve ${s.pretty} = ${t.pretty}")
    // Exhaustively apply Decomp and Abstraction
    val (unsolved, partialSubst) = phase1(vargen, Seq((vargen(s.ty),Seq(),s,t)), Seq(), Subst.id, Subst.id)
    leo.Out.debug(s"Result of phase1:")
    leo.Out.debug(s"unsolved:\n\t${unsolved.map {case (va,de,l,r) =>
      s"${va.pretty}(${de.map(_.pretty).mkString(",")}):" +
        s"${l.pretty} = ${r.pretty}"}.mkString("\n\t")}")
    leo.Out.debug(s"partialSubst: ${partialSubst._1.pretty}")
    // Exhaustively apply Solve
    val (solved, partialSubst2) = phase2(vargen, unsolved, Seq(), partialSubst._1, partialSubst._2)
    leo.Out.debug(s"Result of phase2:")
    leo.Out.debug(s"solved:\n\t${solved.map {case (va,de,l,r) =>
      s"${va.pretty}(${de.map(_.pretty).mkString(",")}):" +
        s"${l.pretty} = ${r.pretty}"}.mkString("\n\t")}")
    leo.Out.debug(s"partialSubst: ${partialSubst2._1.pretty}")
    // Exhaustively apply Merge
    val (merged, (resultSubst, resultTySubst)) = phase3(vargen, solved, partialSubst2._1, partialSubst2._2)


    import leo.datastructures.TermFront
    val resultPattern: Term = resultSubst.substBndIdx(0) match {
      case TermFront(r) => r
      case _ => throw new IllegalArgumentException
    }
    (resultPattern, ???, ???)
  }

  /** Exhaustively applies Decomposition and Abstraction. */
  @tailrec
  private final def phase1(vargen: FreshVarGen,
                           unsolved: Unsolved,
                           processed: Unsolved, partialSubst: TermSubst, partialTySubst: TypeSubst): (Unsolved, FullSubst) = {
    import Term.{Bound, λ, mkTermApp}
    if (unsolved.isEmpty) (processed, (partialSubst.normalize, partialTySubst))
    else {
      val hd = unsolved.head
      // hd is {X(xi): h(ti) = h(si)}
      leo.Out.debug(s"subst: ${partialSubst.normalize.pretty}")
      leo.Out.debug(s"solve: ${hd._1.pretty}(${hd._2.map(_.pretty).mkString(",")}):" +
          s"${hd._3.pretty} = ${hd._4.pretty}")
      assert(Term.wellTyped(hd._3))
      assert(Term.wellTyped(hd._4))
      val canApplyDecomp = Decomposition.canApply(hd)
      if (canApplyDecomp.isDefined) { // See Decomposition for description
        leo.Out.debug("Apply Decomp")
        val absVar = Bound.unapply(hd._1).get._2 // X
        val bound = hd._2 // xi
        val (newUnsolved, newVars, headSymbol) = Decomposition(vargen, hd, canApplyDecomp.get)
        // newUnsolved: {Y1(xi): t1 = s1, ..., Yn(xi): tn = sn}
        // newVars: [Y1, ... Yn]
        // headsymbol: h
        val approxBinding = λ(bound.map(_.ty))(mkTermApp(headSymbol, newVars.map(v => mkTermApp(v.lift(bound.size), bound))))
        // approxBinding: λxi.h(Y1(xi), ... Yn(xi))
        val bindingSubst = Subst.singleton(absVar, approxBinding) // {X -> λxi.h(Y1(xi), ... Yn(xi))}
        phase1(vargen, newUnsolved ++ unsolved.tail, processed, partialSubst.comp(bindingSubst), partialTySubst)
      } else {
        val canApplyAbstraction = Abstraction.canApply(hd)
        if (canApplyAbstraction.isDefined) { // See Abstraction for description
          leo.Out.debug("Apply Abstraction")
          val absVar = Bound.unapply(hd._1).get._2 // X
          val newUnsolved = Abstraction(vargen, hd, canApplyAbstraction.get) // {X'(xi,y): s = t}
          val newVar = newUnsolved._1 // X'
          val bound = newUnsolved._2 // yi,y
          val approxBinding = λ(bound.map(_.ty))(mkTermApp(newVar.lift(bound.size), bound)) // λxi,y.X'(xi,y)
          val bindingSubst = Subst.singleton(absVar, approxBinding) // {X -> λxi,y.X'(xi,y)}
          phase1(vargen, newUnsolved +: unsolved.tail, processed, partialSubst.comp(bindingSubst), partialTySubst)
        } else {
          leo.Out.debug("Apply Nothing")
          phase1(vargen, unsolved.tail, hd +: processed, partialSubst, partialTySubst)
        }
      }

    }
  }

  /** Exhaustively applies Solve. */
  @tailrec
  private final def phase2(vargen: FreshVarGen,
                           unsolved: Unsolved,
                           solved: Solved, partialSubst: TermSubst, partialTySubst: TypeSubst): (Solved, FullSubst) = {
    import Term.{Bound, λ, mkTermApp}
    if (unsolved.isEmpty) (solved, (partialSubst.normalize, partialTySubst))
    else {
      val hd = unsolved.head
      leo.Out.debug(s"subst: ${partialSubst.normalize.pretty}")
      leo.Out.debug(s"solve: ${hd._1.pretty}(${hd._2.map(_.pretty).mkString(",")}):" +
        s"${hd._3.pretty} = ${hd._4.pretty}")
      assert(Term.wellTyped(hd._3))
      assert(Term.wellTyped(hd._4))
      // hd is {X(xi): s = t}
      val absVar = Bound.unapply(hd._1).get._2; val bound = hd._2 // X and xi respectively
      // No need for canApply since the remaining equations should be of the form s = t where
      // head(s) != head(t) or head(s) = head(t) = Z not in xi
      val newSolved = Solve(vargen, hd) // {Y(yi): s = t}
      val newVar = newSolved._1; val newBound = newSolved._2  // Y and yi respectively
      val approxBinding = λ(bound.map(_.ty))(mkTermApp(newVar, newBound)) // λxi.Y(yi)
      val bindingSubst = Subst.singleton(absVar, approxBinding) // {X -> λxi.Y(yi)}
      phase2(vargen, unsolved.tail, newSolved +: solved, partialSubst.comp(bindingSubst), partialTySubst)
    }
  }

  /** Exhaustively applies Merge. */
  private final def phase3(vargen: FreshVarGen,
                           solved: Solved,
                           partialSubst: TermSubst, partialTySubst: TypeSubst): ((Term, Term), FullSubst) = {
    // Traverse all terms in solved to get unique representation (cf. Lemma 4 in paper)

    // partition to alpha-equivalent terms

    // apply merge in each equivalence class

    ???
  }

  /**
    * {{{{X(xi): h(ti) = h(si)} U A; S; σ =>
    *   {Y1(xi): t1 = s1, ..., Yn(xi): tn = sn} U A; S; σ{X <- λxi.h(Y1(xi), ... Yn(xi))} }}}
    *   if `h` is a constant or `h` in `xi`, the `Yi` are fresh.
    */
  object Decomposition {
    /** (head symbol, left args, right args) */
    type DecompHint = (Term, Seq[Term], Seq[Term])
    /** Returns an appropriate [[Decomposition.DecompHint]] if [[Decomposition]] is applicable, `None` otherwise. */
    final def canApply(eq: Eq): Option[DecompHint] = { // TODO: Generalize to polymorphism
      import leo.datastructures.Term.{TermApp, Symbol, Bound}
      val left = eq._3; val right = eq._4
      val bound = eq._2
      left match {
        case TermApp(hd,args1) => right match {
          case TermApp(`hd`,args2) =>
            hd match {
              case Symbol(_) => Some((hd, args1, args2))
              case Bound(_,idx) if idx <= bound.size => Some((hd, args1, args2))
              case _ => None
            }
          case _ => None
        }
        case _ => None
      }
    }
    /** Returns `({Y1(xi): t1 = s1, ..., Yn(xi): tn=sn}, {Y1,..Yn}, h)`
      * @param vargen Vargen
      * @param hint The precomputed values from [[Decomposition#canApply()]].*/
    final def apply(vargen: FreshVarGen, eq: Eq, hint: DecompHint): (Unsolved, Seq[Term], Term) = {
      import leo.datastructures.Type.mkFunType
      val headSymbol = hint._1; val args1 = hint._2; val args2 = hint._3
      assert(args1.length == args2.length)
      val bound = eq._2
      val freshAbstractionVars = args1.map(t => vargen(mkFunType(bound.map(_.ty),t.ty)))
      val newEqs = freshAbstractionVars.zip(args1.zip(args2)).map {case (variable, (arg1, arg2)) =>
        (variable, bound, arg1, arg2)
      }
      (newEqs, freshAbstractionVars, headSymbol)
    }
  }

  /**
    * {{{ {X(xi): λy.t = λz.s} U A; S; σ =>
    *   {X'(xi,y): t = s{z <- y}} U A; S; σ{X <- λxi,y.X'(xi,y)} }}}
    *   where X' is fresh.
    * @note Modified since we use a nameless representation, renaming of z in λz.s is thus unnecessary.
    */
  object Abstraction {
    /** (Type of abstracted variable, body of left abstraction, body of right abstraction) */
    type AbstractionHint = (Type, Term, Term)
    /** Returns an [[Abstraction.AbstractionHint]] if [[Abstraction]] is applicable, `None` otherwise. */
    final def canApply(eq: Eq): Option[AbstractionHint] = {
      import leo.datastructures.Term.:::>
      val left = eq._3; val right = eq._4
      left match {
        case ty :::> bodyLeft => right match {
          case ty2 :::> bodyRight => assert(ty == ty2)
            Some((ty, bodyLeft, bodyRight))
          case _ => None
        }
        case _ => None
      }
    }
    /** Return X'(xi,y): t = s{z <- y}, adjusted to nameless representation.
      * @param vargen Vargen
      * @param hint The already (from [[Abstraction#canApply]]) calculated details for the computation. */
    final def apply(vargen: FreshVarGen, eq: Eq, hint: AbstractionHint): Eq = {
      import leo.datastructures.Term.{Bound, mkBound}
      import leo.datastructures.Type.mkFunType
      val bound = eq._2; val abstractionType = hint._1
      // bound is `xi`, abstractionType is the type of `y`
      val newLeft = hint._2; val newRight = hint._3
      // newLeft and newRight are the bodies of the lambda abstractions (i.e. t and s)
      val newBound = bound.map { t =>
        val (ty, idx) = Bound.unapply(t).get
        mkBound(ty, idx+1)
      } :+ mkBound(abstractionType, 1)
      // newBound is `xi,y`: lift all `xi` by one and add var to it.
      val freshAbstractionVar = vargen(mkFunType(newBound.map(_.ty),newLeft.ty))
      // freshAbstractionVar is `X'`
      (freshAbstractionVar, newBound, newLeft, newRight)
    }
  }

  /**
    * {{{ {X(xi): t = s} U A; S; σ =>
    *   A; {Y(yi): t = s} U S; σ{X <- λxi.Y(yi)} }}}
    *   where `Y` is fresh and the `yi` are those `xi` that occur free in t or s.
    */
  object Solve {
    final def apply(vargen: FreshVarGen, eq: Eq): Eq = {
      import leo.datastructures.Term.Bound
      import leo.datastructures.Type.mkFunType
      val bound = eq._2; val left = eq._3; val right = eq._4
      // bound is `{xi}`, left is `t`, right is `s`
      assert(left.headSymbol != right.headSymbol
        || (Bound.unapply(left.headSymbol).isDefined
            && Bound.unapply(left.headSymbol).get._2 > bound.size))
      val boundOccurrences = left.freeVars union right.freeVars
      val newBound: Seq[Term] = bound.filter (boundOccurrences.contains)
      // newBound is `yi`: those `xi` which occur in left union right.
      val freshAbstractionVar = vargen(mkFunType(newBound.map(_.ty),left.ty)) // Y
      (freshAbstractionVar, newBound, left, right)
    }
  }

  /**
    * {{{A; {X(xi): t1 = t2, Y(yi): s1 = s2} U S; σ =>
    *   A; {X(xi): t1 = t2} U S; σ{Y <- λyi.X(xiπ)} }}}
    *   where π: {xi} -> {yi} is a bijection extended as a substitution  with `t1π = s1` and `t2π = s2`.
    */
  object Merge {
    final def apply(eq1: Eq, eq2: Eq): Any = ???
  }
}
