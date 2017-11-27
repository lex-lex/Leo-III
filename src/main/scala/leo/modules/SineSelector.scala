package leo.modules

import scala.collection.mutable
import leo.datastructures.tptp.Commons.AnnotatedFormula
import leo.modules.SineSelector.TriggerRelation

/**
  * Axiom selector as proposed by Hoder et al. in "Sine Qua Non for Large Theory Reasoning",
  * LNCS 6803.
  */
class SineSelector(triggerRelation: TriggerRelation,
                   definitionOccurrences: Map[String, Set[String]],
                   specialAxioms: Set[AnnotatedFormula]) {
  final def getRelevantAxioms(conjecture: AnnotatedFormula, depth: Int = -1): Seq[AnnotatedFormula] = {
    val conjSymbols = conjecture.function_symbols
    if (conjSymbols.isEmpty) return triggerRelation.values.flatten.toSeq // Is that right?
    val oneTriggeredAxioms = conjSymbols.flatMap(triggerRelation.apply)
    val collectedAxioms: mutable.Set[AnnotatedFormula] = mutable.Set.empty
    var newAxioms: Set[AnnotatedFormula] = oneTriggeredAxioms

    var depthRemaining: Float = if (depth < 0) Float.PositiveInfinity else depth
    while (newAxioms.nonEmpty && depthRemaining > 0) {
      collectedAxioms ++= newAxioms
      val kTriggeredSymbols = newAxioms.flatMap(_.function_symbols)
      val definedSymbols = kTriggeredSymbols.flatMap(definitionOccurrences.apply)
      val newSymbols = kTriggeredSymbols union definedSymbols
      newAxioms = newSymbols.flatMap(triggerRelation.apply) -- collectedAxioms
      depthRemaining -= 1
    }

    (collectedAxioms ++ specialAxioms).toSeq
  }

  override final def toString: String = {
    val sb: mutable.StringBuilder = mutable.StringBuilder.newBuilder
    sb.append("SiNE fact selector instance.\n")
    sb.append("triggerRelation={\n")
    for ((symbol,formulas) <- triggerRelation) {
      sb.append(s"\ttrigger($symbol,${formulas.map(_.name)}), \n")
    }
    sb.append("}")
    sb.toString()
  }
}

object SineSelector {
  type TriggerRelation = Map[String, Set[AnnotatedFormula]]

  final def apply(tolerance: Double, generalityThreshold: Int)
                 (axioms: Seq[AnnotatedFormula], definitions: Seq[AnnotatedFormula]): SineSelector = {
    // occ: symbol -> number of axioms symbol occurs in
    val occ: mutable.Map[String, Int] = mutable.Map.empty
    // defSymbols: Symbol -> set(symbols occurring in definition)
    val defOcc: mutable.Map[String, Set[String]] = mutable.Map.empty
    // triggerRelation: symbol -> set(axioms triggered by symbol)
    val triggerRelation: mutable.Map[String, Set[AnnotatedFormula]] = mutable.Map.empty
    // axioms with no symbols in it. take them.
    val specialAxioms: mutable.Set[AnnotatedFormula] = mutable.Set.empty
    // Step 1. Scan axioms for occurrences
    val axiomsIt = axioms.iterator
    while (axiomsIt.hasNext) {
      val axiom = axiomsIt.next()
      assert(axiom.role == "axiom")
      val symbols = axiom.function_symbols
      if (symbols.isEmpty) {
        specialAxioms += axiom
      } else addOcc(symbols, occ)
    }
    val defsIt = definitions.iterator
    while (defsIt.hasNext) {
      val defi = defsIt.next()
      import leo.datastructures.tptp.Commons._
      import leo.datastructures.tptp.thf.{Logical => THFFormula, Binary => THFBinary, Eq => THFEq, Function => THFFun}
      import leo.datastructures.tptp.tff.{Logical => TFFFormula, Atomic => TFFAtomic }
      defi.f match {
        case THFFormula(THFBinary(THFFun(defName, Seq()), THFEq, definuendum)) => addDefOcc(defName, definuendum.function_symbols, defOcc)
        case TFFFormula(TFFAtomic(Equality(Func(defName, Seq()), definuendum))) => addDefOcc(defName, definuendum.function_symbols, defOcc)
        case _ => ???
      }
    }
    // Step 2. Compute trigger relation
    /*
    trigger (s, A) iff either occ(s) ≤ g or for all symbols s' occurring in A
    we have occ(s) ≤ t · occ(s').
    Note (Alex): This does not say that s has to occur in A at all. But I'm assuming
    that in the following since it would be nonsense to let symbols trigger axioms that do not
    occur in them.
    */
    val axiomsIt2 = axioms.iterator
    while (axiomsIt2.hasNext) {
      val axiom = axiomsIt2.next()
      val symbols = axiom.function_symbols
      if (symbols.nonEmpty) {
        val occs = symbols.map(occ.apply)
        val local_threshold = occs.min * tolerance
        val symbolsIt = axiom.function_symbols.iterator
        while (symbolsIt.hasNext) {
          val s = symbolsIt.next()
          val occS = occ(s)
          if (occS <= generalityThreshold) addTrigger(s, axiom, triggerRelation)
          else if (occS <= local_threshold) addTrigger(s, axiom, triggerRelation)
        }
      }
    }
    new SineSelector(triggerRelation.toMap.withDefaultValue(Set.empty),
      defOcc.toMap.withDefaultValue(Set.empty), specialAxioms.toSet)
  }

  @inline
  private[this] final def addOcc(symbols: Set[String], store: mutable.Map[String, Int]): Unit = {
    val symbolsIt = symbols.iterator
    while (symbolsIt.hasNext) {
      val symbol = symbolsIt.next()
      val maybeValue = store.get(symbol)
      if (maybeValue.isDefined) store += (symbol -> (maybeValue.get + 1))
      else store += (symbol -> 1)
    }
  }

  @inline
  private[this] final def addDefOcc(symbol: String, symbolsInDef: Set[String], store: mutable.Map[String, Set[String]]): Unit = {
    assert(!store.contains(symbol))
    store += (symbol -> symbolsInDef)
  }

  @inline
  private[this] final def addTrigger(symbol: String, formula: AnnotatedFormula, store: mutable.Map[String, Set[AnnotatedFormula]]): Unit = {
    val maybeSet = store.get(symbol)
    if (maybeSet.isDefined) store += (symbol -> (maybeSet.get + formula))
    else store += (symbol -> Set(formula))
  }
}
