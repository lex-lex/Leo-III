package leo.modules.interleavingproc

import java.util.concurrent.atomic.AtomicInteger

import leo.agents.{AbstractAgent, Agent, Task}
import leo.datastructures.{Clause, Signature}
import leo.datastructures.blackboard.{DataType, Event, Result}
import leo.modules.control.Control

/**
  *
  * Processes the delayed Unification in parallel to the main loop
  *
  * @since 11/17/16
  * @author Max Wisniewski
  */
class DelayedUnificationAgent(unificationStore : UnificationStore[InterleavingLoop.A], state : BlackboardState[InterleavingLoop.A], sig : Signature) extends AbstractAgent{
  override val name: String = "DelayedUnificationAgent"
  override val interest: Option[Seq[DataType]] = Some(Seq(OpenUnification))

  override def filter(event: Event): Iterable[Task] = event match {
    case result : Result =>
      val ins = result.inserts(OpenUnification).filter{case a : InterleavingLoop.A => unificationStore.containsUni(a)}
      val rew = state.state.rewriteRules
      val tasks =  ins.map{case a : InterleavingLoop.A => new DelayedUnificationTask(a, this, rew)}
      return tasks
    case _ => Seq()
  }

  override def init(): Iterable[Task] = {
    val ins = unificationStore.getOpenUni
    val rew = state.state.rewriteRules
    ins.map{a => new DelayedUnificationTask(a, this, rew)}
  }

  class DelayedUnificationTask(ac : InterleavingLoop.A, a : DelayedUnificationAgent, rewrite : Set[InterleavingLoop.A]) extends Task {
    override val name: String = "delayedUnification"

    override def run: Result = {
      val result = Result()
      result.remove(OpenUnification)(ac)
      val newclauses = Control.unifyNewClauses(Set(ac))(sig)
      val sb = new StringBuilder("\n")


      val newIt = newclauses.iterator
      if(newIt.isEmpty){
        // Not unifiable. Insert Result
        result.insert(UnprocessedClause)(ac)
      }
      while (newIt.hasNext) {
        var newCl = newIt.next()
        newCl = Control.rewriteSimp(newCl, rewrite)(sig)

        if (!Clause.trivial(newCl.cl)) {
          sb.append(s"Unified Clause:\n>>   ${ac.pretty(sig)}\n>> to\n++> simp  ${newCl.pretty(sig)}")
          result.insert(UnprocessedClause)(newCl)
        }
      }
      sb.append("\n")
      leo.Out.debug(sb.toString())
      result

    }

    override lazy val readSet: Map[DataType, Set[Any]] = Map()
    override lazy val writeSet: Map[DataType, Set[Any]] = Map(OpenUnification -> Set(ac))   // TODO Get writelock?
    override lazy val bid: Double = 0.1
    override val getAgent: Agent = a

    override val pretty: String = s"delayedUnification(${ac.pretty(sig)})"
  }
}

