package leo


import leo.datastructures.blackboard.Blackboard
import leo.datastructures.blackboard.scheduler.Scheduler
import leo.agents.impl.UtilAgents._
import leo.datastructures.context.Context
import leo.modules.output.logger.Out
import leo.modules.{Utility, SZSOutput, CLParameterParser}
import leo.modules.Utility._
import leo.modules.output.SZS_Timeout
import leo.modules.Phase._


/**
 * Entry Point for Leo-III as an executable to
 * proof a TPTP File
 *
 * @author Max Wisniewski
 * @since 7/8/14
 */
object Main {

  /**
   *
   * Tries to proof a Given TPTP file in
   * a given Time.
   *
   * @param args - See [[Configuration]] for argument treatment
   */
  def main(args : Array[String]){
    Configuration.init(new CLParameterParser(args))
    val timeout = Configuration.TIMEOUT
    val interval = 10


    val deferredKill : DeferredKill = (new DeferredKill(interval, Double.PositiveInfinity))
    deferredKill.start()

    // Start scheduler
    Scheduler().signal()

    val it = getStdPhases.iterator
    var r = true
    while(it.hasNext && r) {
      r = it.next().execute()
    }
    deferredKill.kill()

    Out.output(s"%SZS Status ${Blackboard().getStatus(Context()).fold("Unkown")(_.output)} for ${Configuration.PROBLEMFILE}")
    if(Configuration.PROOF_OBJECT) Blackboard().getAll{p => p.clause.isEmpty}.foreach(Utility.printDerivation(_))
  }



  /**
   * Thread to kill leo.
   *
   * TODO: Hook to let the kill Thread die.
   *
   * @param interval
   * @param timeout
   */
  private class DeferredKill(interval : Double, timeout : Double) extends Thread {

    var remain : Double = timeout
    var exit : Boolean = false

    def kill() : Unit = {
      synchronized{
        exit = true
        this.interrupt()
        Scheduler().killAll()
        Out.info("Scheduler killed before timeout.")
      }
    }

    override def run(): Unit = {
      //      println("Init delay kill.")
      synchronized{
        while(remain > 0 && !exit) {
          try {
            val w : Double = if (remain > interval) interval else remain
            wait((w * 1000).toInt)
          } catch {
            case e: InterruptedException => if(exit) return else Thread.interrupted()
            case _: Throwable => ()
          } finally {
            if(!exit) {
              Out.info("Leo is still alive.")
              remain -= interval
            }
          }
        }
        Out.output(SZSOutput(SZS_Timeout))
        Scheduler().killAll()
      }
    }
  }
}

