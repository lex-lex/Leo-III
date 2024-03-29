package leo.modules.input

import java.nio.file.{Files, Path, Paths}
import leo.Out
import leo.datastructures.{Role, Signature, Term, TPTP}
import leo.modules.SZSException
import leo.modules.input.TPTPParser.TPTPParseException
import leo.modules.output.{SZS_InputError, SZS_SyntaxError}

/**
  * This facade object publishes various methods for parsing/processing/reading
  * of TPTP inputs. The method names are as follows by convention:
  *
  * - parseX: Raw input (e.g. string) -> TPTP AST representation
  * - processX: TPTP AST representation -> Term
  * - readX: Raw input (e.g. string) -> Term
  *
  * The most usual methods may be [[Input#readProblem]] and
  * [[Input#readFormula]] for reading a whole
  * TPTP problem and readling a single formula, respectively.
  *
  * @example {{{implicit val s: Signature = ...
  * val t: Term = readFormula("! [X:$i]: (p @ X)")
  * println(t.pretty(s))}}}
  *
  * @author Alexander Steen <a.steen@fu-berlin.de>
  * @since 29.04.2015
  * @note Updated February 2017: Overhaul. Adapted to new InputProcessing and new Parser on January 2021.
  * @see [[leo.datastructures.TPTP]]
  * @see [[leo.datastructures.Term]]
  */
object Input {

  /** Reads the `TPTP` environment variable, e.g. used
    * for parsing objects under TPTP Home. */
  lazy val tptpHome: Path = {
    try {
      val result = canonicalPath(System.getenv("TPTP"))
      result
    } catch {
      case _: Exception =>
        leo.Out.warn("TPTP environment variable not set. Some includes may not be found.")
        null
    }
  }

  ///////////////////////////////////////////////////////////////////////////
  // Functions that go from file/string to unprocessed internal TPTP-syntax
  // "String -> TPTP"
  ///////////////////////////////////////////////////////////////////////////

  /**
    * Reads the file located at `file` and parses it recursively using the `TPTP` parser,
    * hence the file needs to be in valid TPTP format (e.g. FOF, THF, ...).
    * Note that the return value is a sequence of [[leo.datastructures.TPTP.AnnotatedFormula]] since
    * all includes are automatically parsed exhaustively.
    * If `file` is a relative path, it is assumed to be equivalent to the path
    * `user.dir`/file.
    *
    * @note This method has no side effects.
    *
    * @param file  The absolute or relative path to the problem file.
    * @param assumeRead Implicitly assume that the problem files in this parameter
    *                   have already been read. Hence, recursive parsing will skip this
    *                   includes.
    * @return The sequence of annotated TPTP formulae.
    */
  def parseProblemFile(file: String, assumeRead: Set[Path] = Set())(stats: Option[ProblemStatistics] = None): Seq[TPTP.AnnotatedFormula] = {
    // FIXME Assume Read should be a shared between the calls (Dependencies between siblings not detected)
    var result: Seq[TPTP.AnnotatedFormula] = Seq.empty
    val canonicalFile = if (file == "-") canonicalPath(".") else canonicalPath(file) // to allow inputs from CWD if file is stdin
    var assumeRead0 = assumeRead
    Out.trace(s"assumeRead0: ${assumeRead0.map(_.toString).mkString(",")}")
    Out.trace(s"canonicalFile: ${canonicalFile.toString}")
    if (!assumeRead0.contains(canonicalFile)) {
      Out.debug(s"Parsing $file ...")
      val problem: TPTP.Problem = parseProblemFileShallow(file)
      assumeRead0 += canonicalFile
      stats.foreach(_.registerImmediateFormulas(problem.formulas.size))
      val includes = problem.includes
      stats.foreach(_.registerIncludes(includes.size))
      val includesIt = includes.iterator
      Out.trace(s"Found ${includes.size} include(s): ${includes.map(ax => s"'${ax._1}'").mkString(",")}")
      while (includesIt.hasNext) {
        val (includeFile, _) = includesIt.next()
        try {
          val next = canonicalFile.getParent.resolve(includeFile)
          var subResult = parseProblemFile(next.toString, assumeRead0)(None)
          assumeRead0 += canonicalPath(next.toString)
          result ++= subResult
        } catch {
          case e: SZSException =>
            e.status match {
              case SZS_InputError =>
                // If file was not found, it could still be
                // an axiom in the TPTP path, so try again with tptpHome
                if (tptpHome != null) {
                  try {
                    Out.info(s"Included file '$includeFile' not found, trying TPTP home directory ...")
                    val altNext = tptpHome.resolve(includeFile)
                    val altSubResult = parseProblemFile(altNext.toString, assumeRead0)(None)
                    assumeRead0 += canonicalPath(altNext.toString)
                    result ++= altSubResult
                  } catch {
                    case _: Throwable =>
                      throw e
                    // We throw the original exception as we don't
                    // want the alternative file path (with TPTP prefix)
                    // in the error message.
                  }
                } else {
                  Out.info(s"Included file '$includeFile' not found, maybe it is a TPTP axiom and " +
                    s"you forgot to set your TPTP home path ($$TPTP)?")
                  throw e
                }
              case _ => throw e
            }
        }
      }
      stats.foreach(_.registerIncludedFormulas(result.size))
      result ++= problem.formulas
      result
    } else {
      Out.info(s"File '$file' was already parsed, skipping. Maybe it was included multiple times?")
      Seq.empty
    }
  }

  /**
    * Parses the problem represented by `problem` recursively using the `TPTP` parser,
    * hence the string needs to be in valid TPTP format (e.g. FOF, THF, ...).
    * Note that the return value is a sequence of [[leo.datastructures.TPTP.AnnotatedFormula]] since
    * all includes are automatically parsed exhaustively.
    * If the problem contains relative includes they are assumed
    * to be equivalent to includes of `user.dir/...`.
    *
    * @note This method has no side effects.
    *
    * @param problem  The problem as string.
    * @param assumeRead Implicitly assume that the problem files in this parameter
    *                   have already been read. Hence, recursive parsing will skip this
    *                   includes.
    * @return The sequence of annotated TPTP formulae.
    */
  def parseProblem(problem: String, assumeRead: Set[Path] = Set())(stats: Option[ProblemStatistics] = None): Seq[TPTP.AnnotatedFormula] = {
    val p: TPTP.Problem = TPTPParser.problem(problem)
    val includes = p.includes

    // TODO Assume Read should be a shared between the calls (Dependencies between siblings not detected)
    val pIncludes = includes.map{case (inc, _) =>
      try {
        val next = java.nio.file.Paths.get(System.getProperty("user.dir")).resolve(inc)
        parseProblemFile(next.toString, assumeRead)(stats)
      } catch {
        case e : Exception =>
          try {
            if (tptpHome != null) {
              val tnext = tptpHome.resolve(inc)
              parseProblemFile(tnext.toString, assumeRead)(stats)
            } else throw e
          } catch {
            case _ : Exception => throw new SZSException(SZS_InputError, s"The file $inc does not exist.")
          }
      }
    }
    pIncludes.flatten ++ p.formulas
  }

  /**
    * Reads the file located at `file`  and shallowly parses it using the `TPTP` parser, hence
    * the file needs to be in valid tptp format (regardless if FOF, TFF, ...).
    * Note that include statements are *NOT* recursively parsed but returned as TPTP
    * AST instead. For recursive parsing of include statements, use [[Input#parseProblem]].
    * If `file` is a relative path, it is assumed to be equivalent to the path
    * `user.dir`/file.
    *
    * @note This method has no side effects.
    *
    * @param file The absolute or relative path to the problem file.
    * @return The TPTP problem file in [[leo.datastructures.TPTP.Problem]] representation.
    */
  def parseProblemFileShallow(file: String): TPTP.Problem = {
    try {
      TPTPParser.problem(read0(canonicalPath(file)))
    } catch {
      case e: TPTPParseException =>
        throw new SZSException(SZS_SyntaxError, s"Parse error in file '$file' in line ${e.line}:${e.offset}. ${e.getMessage}")
    }
  }

  /**
    * Parses the single TPTP annotated formula given by `formula` into internal
    * TPTP AST representation.
    *
    * @note This method has no side effects.
    *
    * @param formula The formula to be parsed
    * @return The input formula in [[leo.datastructures.TPTP.AnnotatedFormula]] representation.
    */
  def parseAnnotated(formula: String): TPTP.AnnotatedFormula = {
    TPTPParser.annotated(formula)
  }

  /**
    * Parses the single THF logic formula (i.e. without annotations)
    * given by `formula` into internal TPTP AST representation.
    *
    * @note This method has no side effects.
    *
    * @param formula The formula to be parsed without annotations, i.e. a <thf_logic_formula> as given by
    *                THF BNF.
    * @return The input formula in internal [[leo.datastructures.TPTP.THF.Formula]] representation
    * @see [[http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html#thf_logic_formula]] for TPTP THF BNF.
    */
  def parseFormula(formula: String): TPTP.THF.Formula = {
    TPTPParser.thf(formula)
  }

  ///////////////////////////////////////////////////////////////////////////
  // Functions that go from internal TPTP syntax to processed internal representation (Term)
  // "TPTP -> Term"
  ///////////////////////////////////////////////////////////////////////////
  type FormulaId = String

  /**
    * Convert the problem given by the formulae in `problem` to internal term representation.
    * Note that the parameter type is `AnnotatedFormula`, hence
    * all include statements need to be read externally before calling this function.
    *
    * @note  Side effects: Type declarations and definitions within `problem` are added to the signature.
    * @param problem The input problem in [[leo.datastructures.TPTP.AnnotatedFormula]] representation.
    * @return A triple `(id, term, role)` for each `formula` within
    *         `problem`, such that `id` is the identifier of `formula`, `term` is the respective
    *         [[leo.datastructures.Term]] representation of `formula`, and `role` is the role of `formula`
    *         as defined by the TPTP input.
    *         Note that formulae with role [[leo.datastructures.Role_Definition]] or
    *         [[leo.datastructures.Role_Type]] are returned as triples
    *         `(id, LitTrue, role)` with their respective identifier and role.
    */
  def processProblem(problem: Seq[TPTP.AnnotatedFormula])(implicit sig: Signature): Seq[(FormulaId, Term, Role)] = {
    InputProcessing.processAll(sig)(problem)
  }
  /**
    * Convert the `formula` to internal term representation.
    *
    * @note Side effects: If `formula` is a type declaration or a definition,
    * @param formula The input formula in [[leo.datastructures.TPTP.AnnotatedFormula]] representation.
    * @return A triple `(id, term, role)` such that `id` is the identifier of `formula`, `term` is the respective
    *         [[leo.datastructures.Term]] representation of `formula`, and `role` is the role of `formula`
    *         as defined by the TPTP input.
    *         Note that formulae with role [[leo.datastructures.Role_Definition]] or
    *         [[leo.datastructures.Role_Type]] are returned as triples
    *         `(id, LitTrue, role)` with their respective identifier and role.
    */
  def processFormula(formula: TPTP.AnnotatedFormula)(implicit sig: Signature): (FormulaId, Term, Role) = {
    InputProcessing.process(sig)(formula)
  }

  ///////////////////////////////////////////////////////////////////////////
  // Functions that go from file/string to processed internal representation (Term)
  // "String -> Term"
  ///////////////////////////////////////////////////////////////////////////
  /**
    * Reads and recursively parses the file located at `file` and converts its
    * formulae to internal term representation, hence `file` needs to be in valid
    * TPTP syntax.
    * Note that the return value is a sequence of `(formulaId, term, role)` since
    * all includes are automatically parsed and converted exhaustively.
    * If `file` is a relative path, it is assumed to be equivalent to the path
    * `user.dir`/file.
    *
    * @note Side effect: Type declarations and definitions within `problem` are added to the signature.
    *
    * @param file  The absolute or relative path to the problem file.
    * @param assumeProcessed Implicitly assume that the problem files in this parameter
    *                   have already been read and processed.
    *                   Hence, recursive parsing will skip this includes.
    * @return A triple `(id, term, role)` for each `formula` within
    *         `file`, such that `id` is the identifier of `formula`, `term` is the respective
    *         [[leo.datastructures.Term]] representation of `formula`, and `role` is the role of `formula`
    *         as defined by the TPTP input.
    *         Note that formulae with role [[leo.datastructures.Role_Definition]] or
    *         [[leo.datastructures.Role_Type]] are returned as triples
    *         `(id, LitTrue, role)` with their respective identifier and role.
    */
  def readProblem(file: String, assumeProcessed: Set[Path] = Set())(implicit sig: Signature): Seq[(FormulaId, Term, Role)] = {
    processProblem(parseProblemFile(file,assumeProcessed)())(sig)
  }

  /**
    * Reads and parses `formula` and converts it to internal term representation.
    *
    * @note Side effects: Type declarations and definitions within `problem` are added to the signature.
    *
    * @param formula The annotated formula to be parsed and converted.
    * @return A triple `(Id, Term, Role)`,
    *         such that `Id` is the identifier of the formula, `Clause` is the respective
    *         singleton clause in internal representation, and `Role` is the role of the formula as defined
    *         by the TPTP input.
    *         Note that a formula with role `definition` or `type` is returned as a triple
    *         `(Id, Clause($true), Role)` with its respective identifier and role.
    */
  def readAnnotated(formula: String)(implicit sig: Signature): (FormulaId, Term, Role) = {
    processFormula(parseAnnotated(formula))(sig)
  }

  /**
    * Parses and converts a single THF logic formula (i.e. without annotations)
    * given by `formula` into internal term representation.
    *
    * @note This method has no side effects.
    *
    * @param formula The formula to be parsed without annotations, i.e. a <thf_logic_formula> as given by
    *                THF BNF.
    * @return The input formula in internal [[leo.datastructures.Term]] representation
    * @see [[http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html#thf_logic_formula]] for TPTP THF BNF.
    */
  def readFormula(formula: String)(implicit sig: Signature): Term = {
    val parsed = parseFormula(formula)
    InputProcessing.convertTHFFormula(sig)(parsed)
  }
  /** Synonym for [[Input#readFormula]]. */
  def apply(formula: String)(implicit sig: Signature): Term = readFormula(formula)

  final private val urlStartRegex:String  = "(\\w+?:\\/\\/)(.*)"

  /** Converts the input path to a canonical path representation */
  def canonicalPath(path: String): Path = {
    if (path.matches(urlStartRegex)) {
      if (path.startsWith("file://")) {
        Paths.get(path.drop("file://".length)).toAbsolutePath.normalize()
      } else {
        Paths.get(path)
      }
    } else if (path == "-") {
      Paths.get(path)
    } else {
      Paths.get(path).toAbsolutePath.normalize()
    }
  }

  final private val urlStartRegex0:String  = "(\\w+?:\\/)(.*)" // removed one slash because it gets removed by Paths.get(.)
  protected[input] def read0(absolutePath: Path): io.Source = {
    if (absolutePath.toString.matches(urlStartRegex0)) {
      // URL
      io.Source.fromURL(absolutePath.toString.replaceFirst(":/","://"))
    } else {
      if (absolutePath.toString == "-") {
        io.Source.stdin
      } else if (!Files.exists(absolutePath)) { // It either does not exist or we cant access it
        throw new SZSException(SZS_InputError, s"The file ${absolutePath.toString} does not exist or cannot be read.")
      } else io.Source.fromFile(absolutePath.toFile)
    }
  }
}
