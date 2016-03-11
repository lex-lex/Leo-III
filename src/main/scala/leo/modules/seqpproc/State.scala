package leo.modules.seqpproc

import leo.datastructures._
import leo.modules.output.{SZS_Unknown, StatusSZS}

import scala.collection.SortedSet


/**
  * Created by lex on 20.02.16.
  */
abstract class State[T <: ClauseProxy] extends Pretty {

  def signature: IsSignature
  def szsStatus: StatusSZS
  def setSZSStatus(szs: StatusSZS): Unit

  def unprocessed: SortedSet[T]
  def nextUnprocessed: T
  def addUnprocessed(unprocessed: T): Unit
  def addUnprocessed(unprocessed: Set[T]): Unit
  def processed: Set[T]
  def setProcessed(p: Set[T]): Unit
  def addProcessed(cl: T): Unit

  def rewriteRules: Set[T]
  def addRewriteRule(cl: T): Unit

  def setDerivationClause(cl: T): Unit
  def derivationClause: Option[T]

  // Statistics
  def noProcessedCl: Int
  def incTrivialCl(): Unit
  def noTrivialCl: Int
  def incForwardSubsumedCl(): Unit
  def noForwardSubsumedCl: Int
  def incBackwardSubsumedCl(): Unit
  def noBackwardSubsumedCl: Int
  def incGeneratedCl(by: Int): Unit
  def noGeneratedCl: Int
  def incParamod(by: Int): Unit
  def noParamod: Int
  def incFactor(by: Int): Unit
  def noFactor: Int
}

protected[seqpproc] class StateImpl[T <: ClauseProxy](initSZS: StatusSZS, initSignature: IsSignature)
                                                     (implicit unprocessedOrdering: Ordering[T]) extends State[T] {
  private var current_szs = initSZS
  private val sig: IsSignature = initSignature
  private var current_unprocessed: SortedSet[T] = SortedSet()(unprocessedOrdering)
  private var current_processed: Set[T] = Set()
  private var current_rewriterules: Set[T] = Set()
  private var derivationCl: Option[T] = None

  override def signature: IsSignature = sig
  override def szsStatus: StatusSZS = current_szs
  override def setSZSStatus(szs: StatusSZS): Unit =  {current_szs = szs}

  override def unprocessed: SortedSet[T] = current_unprocessed
  override def nextUnprocessed: T = {
    val next = current_unprocessed.head
    current_unprocessed = current_unprocessed.tail
    next
  }
  override def addUnprocessed(cl: T): Unit = {current_unprocessed = current_unprocessed + cl}
  override def addUnprocessed(cls: Set[T]): Unit = {current_unprocessed = current_unprocessed union cls}
  override def processed: Set[T] = current_processed
  override def setProcessed(c: Set[T]): Unit = {current_processed = c}
  override def addProcessed(cl: T): Unit = { current_processed = current_processed + cl }

  override def rewriteRules: Set[T] = current_rewriterules
  override def addRewriteRule(cl: T): Unit = {current_rewriterules = current_rewriterules + cl}

  override def setDerivationClause(cl: T): Unit = {derivationCl = Some(cl)}
  override def derivationClause: Option[T] = derivationCl

  // Statistics
  private var generatedCount: Int = 0
  private var rewriteCount: Int = 0
  private var trivialCount: Int = 0
  private var forwardSubsumedCount: Int = 0
  private var backwardSubsumedCount: Int = 0
  private var factorCount: Int = 0
  private var paramodCount: Int = 0

  override def noProcessedCl: Int = processed.size
  override def noGeneratedCl: Int = generatedCount
  override def noTrivialCl: Int = trivialCount
  override def noParamod: Int = paramodCount
  override def noFactor: Int = factorCount
  override def noForwardSubsumedCl: Int = forwardSubsumedCount
  override def noBackwardSubsumedCl: Int = backwardSubsumedCount

  override def incGeneratedCl(by: Int): Unit = {generatedCount += by}
  override def incTrivialCl(): Unit = {trivialCount += 1}
  override def incParamod(by: Int): Unit = {paramodCount += by}
  override def incFactor(by: Int): Unit = {factorCount += by}
  override def incForwardSubsumedCl(): Unit = {forwardSubsumedCount += 1}
  override def incBackwardSubsumedCl(): Unit = {backwardSubsumedCount += 1}

  // Pretty
  override def pretty: String = s"State SZS: ${szsStatus.pretty}, #processed: ${noProcessedCl}"
}

object State {
  def fresh[T <: ClauseProxy](sig: IsSignature)(implicit unprocessedOrdering: Ordering[T]): State[T] =
    new StateImpl[T](SZS_Unknown, sig)(unprocessedOrdering)
}