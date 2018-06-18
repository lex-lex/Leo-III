package leo.modules.external

import java.io.{File, PrintWriter}

import leo.Configuration
import leo.datastructures.{Clause, ClauseProxy, Signature}
import leo.modules.output._

/**
  *
  * Capsules the call to an atp system with SZS conform return syntax.
  *
  * @since 1/17/17
  * @author Max Wisniewski
  *
  */
trait TptpProver[C <: ClauseProxy] extends HasCapabilities { self =>
  /** The name of the prover. */
  def name : String

  /** The path for the prover. */
  def path : String

  def szsOutputStartDelim: Seq[String] = Seq(TptpProver.SZS_OUTPUT_START_DELIM)
  def szsOutputEndDelim: Seq[String] = Seq(TptpProver.SZS_OUTPUT_END_DELIM)

  /**
    * Calls the external prover on a set of formulas assumed to be correct.
    *
    * @param problemOrigin the clauseproxys the `concreteProblem` originates from
    * @param concreteProblem the set of clauses to be sent to the prover
    * @param sig the signature under which `concreteProblem` is represented
    * @param callLanguage The TPTP language in which the call should be formatted
    * @param timeout the timeout for the prover in seconds
    *
    * @return A Future with the result of the prover.
    */
  def call(problemOrigin: Set[C], concreteProblem: Set[Clause],
           sig: Signature, callLanguage: Capabilities.Language,
           timeout : Int,
          extraArgs: Seq[String] = Seq.empty): Future[TptpResult[C]] = {
    leo.Out.debug(s"Calling prover $name")
    val translatedProblem = translateProblem(concreteProblem, callLanguage)(sig)
    if (Configuration.isSet("atpdebug")) {
      leo.Out.output(s"produced problem: #original facts ${problemOrigin.size}, #facts sent: ${concreteProblem.size}")
    }
    startProver(translatedProblem, problemOrigin, timeout, extraArgs)
  }

  /**
    * Constructs the resulting call for the prover.
    * Important are the nameing of the timeout and where to put the problem file.
    *
    * @param args Additional arguments for the prover
    * @param timeout The timeout in seconds
    * @param problemFileName The name of the problemfile in TPTP syntax
    * @return
    */
  protected def constructCall(args : Seq[String], timeout: Int, problemFileName : String) : Seq[String]

  /**
    * Translates the problem to a problem in TPTP syntax.
    *
    * @param problem Set of clauses to be sent to the external prover
    * @param language The goal language to translate to (e.g. THF, TFF, ...)
    */
  protected[external] def translateProblem(problem : Set[Clause], language: Capabilities.Language)(implicit sig : Signature) : String = {
    if (!capabilities.contains(language)) throw new IllegalArgumentException(s"Prover $name does not support the given language.")
    else {
      if (language == Capabilities.THF) createTHFProblem(problem)(sig)
      else if (language == Capabilities.TFF) createTFFProblem(problem)(sig)
      else if (language == Capabilities.FOF) throw new NotImplementedError("FOF export not yet implemented")
      else if (language == Capabilities.CNF) throw new NotImplementedError("CNF export not yet implemented")
      else throw new IllegalArgumentException("unexpected TPTP output format")
    }
  }

  /** Start the computation of the external prover. Returns immediately a [[leo.modules.external.Future]]
    * that will contain the result of the call. */
  final private def startProver(translatedProblem: String, originalProblem: Set[C],
                                 timeout: Int,
                                 args: Seq[String] = Seq.empty): Future[TptpResult[C]] = {
    /* write problem to temporary file */
    val safeProverName = java.net.URLEncoder.encode(name, "UTF-8") // used as filename
    val file = File.createTempFile(s"remoteInvoke_${safeProverName}_", ".p")
    if (!Configuration.isSet("overlord")) file.deleteOnExit()
    try {
      val writer = new PrintWriter(file)
      try {
        writer.print(translatedProblem)
        writer.flush()
      } catch {
        case e: Exception => leo.Out.warn(e.toString)
      } finally {
        writer.close()
      }
    } catch {
      case e: Exception => leo.Out.warn(e.toString)
    }
    /* invoke prover as external process */
    if (Configuration.isSet("atpdebug")) {
      leo.Out.output(s"produced file: ${file.getName}, file size: ${file.length()}")
      leo.Out.output(s"Extra args: ${args.toString()}")
    }
    val callCmd = constructCall(args, timeout, file.getAbsolutePath)
    if (Configuration.isSet("atpdebug")) {
      leo.Out.output(s"Call constructed: ${callCmd.mkString(" ")}")
    }
    val extProcess = new ProcessBuilder(callCmd:_*)
    /* wrap it as future result */
    new TPTPResultFuture(extProcess, originalProblem, timeout)
  }

  protected[TptpProver] class TptpResultImpl(originalProblem : Set[C],
                                             passedSzsStatus : StatusSZS,
                                             passedSzsOutput: Option[String],
                                             passedExitValue : Int,
                                             passedOutput : Iterable[String],
                                             passedError : Iterable[String]) extends TptpResult[C] {
    /**
      * The name of the original prover called..
      * @return prover name
      */
    val proverName : String = name

    val prover: TptpProver[C] = self

    /**
      * The path of the original prover.
      * @return prover path
      */
    val proverPath : String = path

    /**
      * Returns the original problem, passed to the external prover
      * @return
      */
    val problem : Set[C] = originalProblem

    /**
      * The SZS status of the external prover if one was set
      * or [[leo.modules.output.SZS_Forced]] if the process was killed.
      *
      * @return SZSStatus of the problem
      */
    val szsStatus : StatusSZS = passedSzsStatus
    val szsOutput: Option[String] = passedSzsOutput

    /**
      * The exit value of the prover
      * @return Passed through exitValue
      */
    val exitValue : Int = passedExitValue

    /**
      * The complete system output of the prover.
      *
      * @return system out
      */
    val output : Iterable[String] = passedOutput

    /**
      * The complete system error of the prover
      *
      * @return system err
      */
    val error : Iterable[String] = passedError
  }

  protected final class TPTPResultFuture(process: ProcessBuilder,
                                         originalProblem: Set[C],
                                         timeout: Int) extends Future[TptpResult[C]] {


    /* internal definitions */
    private val stdoutAnswer: StringBuilder = new StringBuilder
    private val stderrAnswer: StringBuilder = new StringBuilder
    private var result: TptpResult[C] = _
    private var terminated: Boolean = false

    /* start the computation */
    private val process0: Process = process.start()

    /* member definitions */
    def isCompleted: Boolean = synchronized{ isCompleted0 }

    private def isCompleted0: Boolean = {
      if (terminated) true
      else {
        if (process0.isAlive) false
        else {
          terminated = true
          generateResult()
          true
        }
      }
    }

    def value: Option[TptpResult[C]] = synchronized{ Option(result) }

    def blockValue: TptpResult[C] = synchronized{ blockValue0 }

    private def blockValue0: TptpResult[C] = {
      if (terminated) result
      else {
        while (!terminated) {
          try {
            process0.waitFor()
            terminated = true
          } catch {
            case _:InterruptedException => // nop
          }
        }
        generateResult()
        result
      }
    }

    def kill(): Unit = process0.destroyForcibly()

    /**
      * Performs a translation of the result of the external process.
      * by reading the stdOut and searching for
      * TPTP conform SZS result. If not existent,set SZS_GaveUp
      */
    private def generateResult(): Unit = try {
      assert(terminated)
      val exitCode = process0.exitValue()
      val stdin = scala.io.Source.fromInputStream(process0.getInputStream).getLines().toSeq
      val stderr = scala.io.Source.fromInputStream(process0.getErrorStream).getLines().toSeq

      val errorMsg = stderr.mkString("\n")
      if (errorMsg != "") leo.Out.warn(s"Error message from $name:\n$errorMsg")

      val szsAnswer = atpAnswerToSZS(stdin.iterator)
      val szsOutput = atpSZSOutput(stdin.iterator)

      if (Configuration.isSet("atpdebug")) {
        val answer = stdin.mkString("\n")
        leo.Out.output("#############################")
        leo.Out.output("name:" + name)
        leo.Out.output("--------------------")
        leo.Out.output("output:\n" + answer)
        leo.Out.output("--------------------")
        leo.Out.output("szs status:\n" + szsAnswer())
        leo.Out.output("--------------------")
        leo.Out.output("szs output:\n" + szsOutput.getOrElse("<nothing>"))
        leo.Out.output("--------------------")
        if (answer.contains("error")) {
          leo.Out.output("+-+-+-+-+-+-+-+-+-+-+-+-+ Melon Melon!")
          originalProblem.foreach(c => leo.Out.output(c.pretty))
          leo.Out.output("+-+-+-+-+-+-+-+-+-+-+-+-+ Melon Melon!")
          throw new Error
        }
      }

      result = new TptpResultImpl(originalProblem, szsAnswer, szsOutput, exitCode,
        stdoutAnswer.lines.toIterable, stderrAnswer.lines.toIterable)
    } catch {
      case e : Exception =>
        val error = if(Configuration.isSet("atpdebug")) Seq(e.toString) else Seq()
        result =  new TptpResultImpl(originalProblem, SZS_Error, null, -1,
        Seq(), error)
    }

    private def atpAnswerToSZS(stdin: Iterator[String]): StatusSZS = {
      var szsStatus: StatusSZS = null
      while (stdin.hasNext && szsStatus == null) {
        val line = stdin.next()
        StatusSZS.answerLine(line) match {
          case Some(status) => szsStatus = status
          case _ => ()
        }
      }
      if (szsStatus == null) SZS_GaveUp else szsStatus
    }
    private def atpSZSOutput(stdin: Iterator[String]): Option[String] = {
      val sb: StringBuilder = new StringBuilder
      var started: Boolean = false
      var finished: Boolean = false
      while (stdin.hasNext && !finished) {
        val line = stdin.next().trim
        if (szsOutputStartDelim.exists(line.startsWith)) started = true
        else if (szsOutputEndDelim.exists(line.startsWith)) finished = true
        else {
          if (started) {
            sb.append(line)
            sb.append('\n')
          }
        }
      }
      if (sb.isEmpty) None else Some(sb.toString())
    }
  }
}
object TptpProver {
  final val SZS_OUTPUT_START_DELIM = "% SZS output start"
  final val SZS_OUTPUT_END_DELIM = "% SZS output end"
}


trait TptpResult[C <: ClauseProxy] {
  /**
    * The name of the original prover called..
    * @return prover name
    */
  @deprecated("Use prover.name instead.", "2.13")
  def proverName : String

  /**
    * The TPTP prover that produces that result.
    */
  def prover: TptpProver[C]

  /**
    * The path of the original prover.
    * @return prover path
    */
  def proverPath : String

  /**
    * Returns the original problem, passed to the external prover
    * @return
    */
  def problem : Set[C]

  /**
    * The SZS status of the external prover if one was set
    * or [[leo.modules.output.SZS_Forced]] if the process was killed.
    *
    * @return SZSStatus of the problem
    */
  def szsStatus : StatusSZS
  /** The prover output as defined by the SZS ontology, if existent.
    * Note that this is the substring of [[output]] between "% SZS output start"
    * and "% SZS output end". */
  def szsOutput: Option[String]

  /**
    * The exit value of the prover
    * @return Passed through exitValue
    */
  def exitValue : Int

  /**
    * The complete system output of the prover.
    *
    * @return system out
    */
  def output : Iterable[String]

  /**
    * The complete system error of the prover
    *
    * @return system err
    */
  def error : Iterable[String]
}

/**
  * A smaller interface for scala's [[scala.concurrent.Future]] class.
  * Implements the bare necessities for a Future in this setting.
  *
  * @tparam T - Type of the Result of the Future
  */
trait Future[+T] {
  /**
    * Checks for the processes termination.
    * @return true, iff the processes has finished.
    */
  def isCompleted : Boolean

  /**
    * Returns the result object after the process has finished.
    *
    * @return Some(result) if the process has finished, None otherwise.
    */
  def value : Option[T]

  /**
    * Blocks until the value is set.
    * After a call to blockValue isCompleted will return true and `value` will
    * always return the value of blockValue.
    * @return
    */
  def blockValue : T

  /**
    * Forcibly kills the underlying process calculating the future's result.
    */
  def kill(): Unit
}
