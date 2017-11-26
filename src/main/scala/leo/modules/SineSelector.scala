package leo.modules

import scala.collection.mutable
import leo.datastructures.tptp.Commons.AnnotatedFormula
import leo.modules.SineSelector.TriggerRelation

/**
  * Axiom selector as proposed by Hoder et al. in "Sine Qua Non for Large Theory Reasoning",
  * LNCS 6803.
  */
class SineSelector(tolerance: Double, generalityThreshold: Int,triggerRelation: TriggerRelation) {
  final def getRelevantAxioms(conjecture: AnnotatedFormula)(depth: Int): Seq[AnnotatedFormula] = ???

  override final def toString: String = {
    val sb: mutable.StringBuilder = mutable.StringBuilder.newBuilder
    sb.append("SiNE fact selector instance.\n")
    sb.append(s"tolerance=$tolerance, generalityThreshold=$generalityThreshold, ")
    sb.append("triggerRelation={\n")
    for ((symbol,formulas) <- triggerRelation) {
      sb.append(s"\ttrigger($symbol,${formulas.map(_.name)}),\n")
    }
    sb.append("}")
    sb.toString()
  }
}

object SineSelector {
  type TriggerRelation = Map[String, Set[AnnotatedFormula]]

  final def apply(tolerance: Double, generalityThreshold: Int)
                 (axioms: Seq[AnnotatedFormula]): SineSelector = {
    // occ: symbol -> number of axioms symbol occurs in
    val occ: mutable.Map[String, Int] = mutable.Map.empty
    // triggerRelation: symbol -> set(axioms triggered by symbol)
    val triggerRelation: mutable.Map[String, Set[AnnotatedFormula]] = mutable.Map.empty
    // Step 1. Scan axioms for occurrences
    val axiomsIt = axioms.iterator
    while (axiomsIt.hasNext) {
      val axiom = axiomsIt.next()
      assert(axiom.role == "axiom")
      addOcc(axiom.function_symbols, occ)
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
    new SineSelector(tolerance, generalityThreshold, triggerRelation.toMap)
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
  private[this] final def addTrigger(symbol: String, formula: AnnotatedFormula, store: mutable.Map[String, Set[AnnotatedFormula]]): Unit = {
    val maybeSet = store.get(symbol)
    if (maybeSet.isDefined) store += (symbol -> (maybeSet.get + formula))
    else store += (symbol -> Set(formula))
  }
}
