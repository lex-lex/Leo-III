package leo.modules.prover

import leo.datastructures._
import leo.modules.{FVState, FVStateImpl, GeneralState, Proof}
import leo.modules.external.{Future, TptpProver, TptpResult}
import leo.modules.prover.State.LastCallStat

import scala.ref.WeakReference

/**
  * Created by lex on 20.02.16.
  */
trait State[T <: ClauseProxy] extends FVState[T] {
  def initUnprocessed(): Unit
  def unprocessedLeft: Boolean
  def unprocessed: Set[T]
  def nextUnprocessed: T
  def addUnprocessed(unprocessed: T): Unit
  def addUnprocessed(unprocessed: Set[T]): Unit
  def removeUnprocessed(unprocessed: Set[T]): Unit
  def processed: Set[T]
  def addProcessed(cl: T): Unit
  def removeProcessed(cls: Set[T]): Unit

  def proof: Proof
  def setProof(proof: Proof): Unit

  def rewriteRules: Set[T]
  def addRewriteRule(cl: T): Unit
  def nonRewriteUnits: Set[T]
  def addNonRewriteUnit(cl: T): Unit
  def removeUnits(cls: Set[T]): Unit

  type Problem = Set[T]
  case class EnqueuedProblem(problem: Problem, translated: Boolean)
  type OpenCall = Future[TptpResult[T]]
  def openExtCalls: Map[TptpProver[T], Set[OpenCall]]
  def removeOpenExtCalls(prover: TptpProver[T], calls: Set[OpenCall]): Unit
  def addOpenExtCall(prover: TptpProver[T], call: OpenCall): Unit
  def nextQueuedCall(prover: TptpProver[T]): Problem
  def enqueuedCalls(prover: TptpProver[T]): Set[Problem]
  def enqueueCall(prover: TptpProver[T], problem: Problem): Unit

  def incTranslations: Int
  def decTranslations: Int
  def getTranslations: Int

  def lastCall: LastCallStat[T]
  def setLastCallStat(lcs: LastCallStat[T]): Unit

  def copy : State[T]

  protected[prover] def queues(): MultiPriorityQueue[T]
  protected[prover] def clauseCache: Map[Long, WeakReference[T]]
}

object State {
  def fresh[T <: ClauseProxy](sig: Signature): State[T] = new StateImpl[T](sig)

  abstract class LastCallStat[T <: ClauseProxy] {
    private var lastLoopCount0: Long = 0
    private var lastProcessedSize0: Int = 0
    private var lastTime0: Long = 0
    private var lastProblem0: Set[T] = _

    def lastLoopCount: Long = lastLoopCount0
    def lastProcessedSize: Int = lastProcessedSize0
    def lastTime: Long = lastTime0
    def lastProblem: Set[T] = if (lastProblem0 == null) Set.empty else lastProblem0

    def shouldCall(problem: Set[T])(implicit state: State[T]): Boolean

    def calledNow(problem: Set[T])(implicit state: State[T]): Unit = {
      lastLoopCount0 = state.noProofLoops
      lastProcessedSize0 = state.noProcessedCl
      lastTime0 = System.currentTimeMillis()
      lastProblem0 = problem
    }

    def fresh: LastCallStat[T]
  }
}

protected[prover] class StateImpl[T <: ClauseProxy](initSignature: Signature) extends FVStateImpl[T](initSignature) with State[T]{
  private var current_processed: Set[T] = Set()
  private var current_rewriterules: Set[T] = Set()
  private var current_nonRewriteUnits: Set[T] = Set()

  private final val sig: Signature = initSignature
  private final val mpq: MultiPriorityQueue[T] = MultiPriorityQueue.empty
  def queues(): MultiPriorityQueue[T] = mpq
  var clauseCache: Map[Long, WeakReference[T]] = Map.empty
  private var openExtCalls0: Map[TptpProver[T], Set[Future[TptpResult[T]]]] = Map.empty
  private var queuedTranslations : Int = 0
  private var extCallStat: LastCallStat[T] = _
  private var queuedExtCalls0: Map[TptpProver[T], Vector[Set[T]]] = Map.empty

  private var proof0: Proof = _

  def proof: Proof = proof0
  def setProof(proof: Proof): Unit = {proof0 = proof}

  def openExtCalls: Map[TptpProver[T], Set[Future[TptpResult[T]]]] = openExtCalls0
  def lastCall: LastCallStat[T] = extCallStat
  def setLastCallStat(lcs: LastCallStat[T]): Unit = {extCallStat = lcs}
  def removeOpenExtCalls(prover: TptpProver[T], calls: Set[Future[TptpResult[T]]]): Unit = {
    if (openExtCalls0.isDefinedAt(prover)) {
      val openCalls = openExtCalls0(prover)
      val newCalls = openCalls diff calls
      if (newCalls.isEmpty) openExtCalls0 = openExtCalls0 - prover
      else openExtCalls0 = openExtCalls0 + (prover -> newCalls)
    }
  }
  def addOpenExtCall(prover: TptpProver[T], call: Future[TptpResult[T]]): Unit = {
    if (openExtCalls0.isDefinedAt(prover)) {
      val openCalls = openExtCalls0(prover)
      openExtCalls0 = openExtCalls0 + (prover -> openCalls.+(call))
    } else {
      openExtCalls0 = openExtCalls0 + (prover -> Set(call))
    }
  }



  override def incTranslations: Int = synchronized{
    queuedTranslations += 1
    queuedTranslations
  }

  override def decTranslations: Int = synchronized{
    queuedTranslations -= 1
    queuedTranslations
  }

  override def getTranslations: Int = synchronized{
    queuedTranslations
  }

  type Pick = Boolean
  val HEAD: Pick = false
  val TAIL: Pick = true

  var lastPick: Pick = HEAD

  def nextQueuedCall(prover: TptpProver[T]): Set[T] = {
    if (queuedExtCalls0.isDefinedAt(prover)) {
      val list = queuedExtCalls0(prover)
      if (list.isEmpty) throw new NoSuchElementException("nextQueueCall on empty queueExtCalls entry")
      else {
        val (result, newList) = if (lastPick == HEAD) {
          lastPick = TAIL
          (list.last, list.init)
        } else {
          lastPick = HEAD
          (list.head, list.tail)
        }
        queuedExtCalls0 = queuedExtCalls0 + (prover -> newList)
        result
      }
    } else {
      throw new NoSuchElementException("nextQueueCall on empty queueExtCalls")
    }
  }
  def enqueuedCalls(prover: TptpProver[T]): Set[Problem] = {
    if (queuedExtCalls0.isDefinedAt(prover)) {
      queuedExtCalls0(prover).toSet
    } else Set.empty
  }
  def enqueueCall(prover: TptpProver[T], problem: Set[T]): Unit = {
    if (queuedExtCalls0.isDefinedAt(prover)) {
      val list = queuedExtCalls0(prover)
      val list0 = list :+ problem
      queuedExtCalls0 = queuedExtCalls0 + (prover -> list0)
    } else {
      queuedExtCalls0 = queuedExtCalls0 + (prover -> Vector(problem))
    }
  }


  override final def copy: State[T] = {
    val state = new StateImpl[T](initSignature.copy)
    state.current_szs = current_szs
    state.conjecture0 = conjecture0
    state.negConjecture0 = negConjecture0
    state.current_processed = current_processed
    state.current_rewriterules = current_rewriterules
    state.current_nonRewriteUnits = current_nonRewriteUnits
    state.derivationCl = derivationCl
    state.current_externalProvers = current_externalProvers
    state.runStrategy0 = runStrategy0
    state.symbolsInConjecture0 = symbolsInConjecture0
    state.choiceFunctions0 = choiceFunctions0
    state.initialProblem0 = initialProblem0
    state.poly = poly
    state.current_externalProvers = current_externalProvers
    state.timeout0 = timeout0
    state.domainConstr0 = domainConstr0
    if (lastCall != null) state.extCallStat = lastCall.fresh
    state
  }

  override final def copyGeneral : GeneralState[T] = {
    val state = new StateImpl[T](sig)
    state.current_szs = current_szs
    state.conjecture0 = conjecture0
    state.negConjecture0 = negConjecture0
    state.current_processed = current_processed
    state.current_rewriterules = current_rewriterules
    state.current_nonRewriteUnits = current_nonRewriteUnits
    state.derivationCl = derivationCl
    state.current_externalProvers = current_externalProvers
    state.runStrategy0 = runStrategy0
    state.symbolsInConjecture0 = symbolsInConjecture0
    state.choiceFunctions0 = choiceFunctions0
    state.initialProblem0 = initialProblem0
    state.poly = poly
    state.current_externalProvers = current_externalProvers
    state.timeout0 = timeout0
    state.domainConstr0 = domainConstr0
    state
  }
  override def copyFVState: FVState[T] = copy

  final def initUnprocessed(): Unit = {
    import leo.datastructures.ClauseProxyOrderings._
    val conjSymbols: Set[Signature.Key] = symbolsInConjecture0
    mpq.addPriority(litCount_conjRelSymb(conjSymbols, 0.005f, 100, 50).asInstanceOf[Ordering[T]])
    mpq.addPriority(goals_SymbWeight(100,20).asInstanceOf[Ordering[T]])
    mpq.addPriority(goals_litCount_SymbWeight(100,20).asInstanceOf[Ordering[T]])
    mpq.addPriority(nongoals_litCount_SymbWeight(100,20).asInstanceOf[Ordering[T]])
    mpq.addPriority(conjRelSymb(conjSymbols, 0.005f, 100, 50).asInstanceOf[Ordering[T]])
    mpq.addPriority(sos_conjRelSymb(conjSymbols, 0.05f, 2, 1).asInstanceOf[Ordering[T]])
    mpq.addPriority(oldest_first.asInstanceOf[Ordering[T]])
  }
  final def unprocessedLeft: Boolean = !mpq.isEmpty
  final def unprocessed: Set[T] = {
    if (mpq == null) leo.Out.comment("MPQ null")
    mpq.toSet
  }
  final private val prio_weights = Seq(10,1,1,2,10,2,1)
  private var cur_prio = 0
  private var cur_weight = 0
  final def nextUnprocessed: T = {
    leo.Out.trace(s"[###] Selecting with priority $cur_prio: element $cur_weight")
    leo.Out.trace(s"[###] mpq.priorities ${mpq.priorityCount}")
    if (cur_weight > prio_weights(cur_prio)-1) {
      leo.Out.trace(s"[###] limit exceeded (limit: ${prio_weights(cur_prio)}) (cur_weight: $cur_weight)")
      cur_weight = 0
      cur_prio = (cur_prio + 1) % mpq.priorityCount
      leo.Out.trace(s"[###] cur_prio set to $cur_prio")
    }
    val result = mpq.dequeue(cur_prio)
    cur_weight = cur_weight+1
    result
  }

  final def addUnprocessed(cl: T): Unit = {mpq.insert(cl); clauseCache += (cl.id -> WeakReference(cl))}
  final def addUnprocessed(cls: Set[T]): Unit = {mpq.insert(cls); cls.foreach {cl => clauseCache += (cl.id -> WeakReference(cl))}}
  final def removeUnprocessed(cls: Set[T]): Unit = {mpq.remove(cls)}

  final def processed: Set[T] = current_processed
  final def addProcessed(cl: T): Unit = { current_processed = current_processed + cl }
  final def removeProcessed(cls: Set[T]): Unit = {current_processed = current_processed -- cls}

  final def rewriteRules: Set[T] = current_rewriterules
  final def addRewriteRule(cl: T): Unit = {current_rewriterules = current_rewriterules + cl}
  final def nonRewriteUnits: Set[T] = current_nonRewriteUnits
  final def addNonRewriteUnit(cl: T): Unit = {current_nonRewriteUnits = current_nonRewriteUnits + cl}
  final def removeUnits(cls: Set[T]): Unit = {
    current_rewriterules = current_rewriterules diff cls
    current_nonRewriteUnits = current_nonRewriteUnits diff cls
  }

  final override def noProcessedCl: Int = processed.size

  // Pretty
  override final def pretty: String = s"State SZS: ${szsStatus.pretty}, #processed: $noProcessedCl"
}

class FVIndex {
  import leo.modules.indexing.{CFF, FVIndex}

  val maxFeatures: Int = 100
  var initialized = false
  var features: Seq[CFF] = Vector.empty
  var index = FVIndex()
  def clauseFeatures: Seq[CFF] = features

  protected[modules] final def reset(): Unit = {
    initialized = false
    features = Vector.empty
    index = FVIndex()
  }
}
