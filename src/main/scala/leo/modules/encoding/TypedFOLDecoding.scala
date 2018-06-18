package leo.modules.encoding

import leo.datastructures.tptp.Commons.{TFFAnnotated, THFAnnotated}
import leo.datastructures.tptp.tff.{Formula => TFFFormula, LogicFormula => TFFLogicFormula}
import leo.datastructures.tptp.thf.{Formula => THFFormula, LogicFormula => THFLogicFormula}

object TypedFOLDecoding {
  def apply(formula: TFFAnnotated): THFAnnotated = {
    val name = formula.name
    val role = formula.role
    val formula0 = formula.formula
//    val anno = formula.annotations
    THFAnnotated(name, role, decodeTFFFormula(formula0), None)
  }

  private def decodeTFFFormula(formula: TFFFormula): THFFormula = {
    import leo.datastructures.tptp.tff.{Logical => TFFLogical, TypedAtom => TFFTypedAtom}
    import leo.datastructures.tptp.thf.{Logical => THFLogical, Typed => THFTyped, Function => THFFunction}
    formula match {
      case TFFLogical(f) => THFLogical(decodeTFFLogicFormula(f))
      case TFFTypedAtom(name, ty) => THFLogical(THFTyped(THFFunction(name, Seq.empty),decodeTFFType(ty).get))
      case _ => // this should not happen
        null
    }
  }

  private def decodeTFFLogicFormula(formula: TFFLogicFormula): THFLogicFormula = {
    import leo.datastructures.tptp.tff.{Binary => TFFBinary,
      Quantified => TFFQuantified, Unary => TFFUnary, Inequality => TFFInequality,
      Atomic => TFFAtomic, Cond => TFFCond, Let => TFFLet}
    import leo.datastructures.tptp.tff.{AtomicType => TFFAtomicType}
    import leo.datastructures.tptp.thf.{Binary => THFBinary, Quantified => THFQuantified,
    Unary => THFUnary, Cond => THFCond}
    formula match {
      case TFFBinary(left, conn, right) =>
        val decodedLeft = decodeTFFLogicFormula(left)
        val decodedRight = decodeTFFLogicFormula(right)
        val decodedConn = decodeTFFConnective(conn)
        THFBinary(decodedLeft, decodedConn, decodedRight)
      case TFFQuantified(q, varList, matrix) =>
        val decodedConn = decodeTFFConnective(q)
        val decodedVarList = varList.map {vari =>
          (vari._1, decodeTFFType(vari._2.getOrElse(TFFAtomicType("$i", Seq.empty))))
        }
        val decodedMatrix = decodeTFFLogicFormula(matrix)
        THFQuantified(decodedConn, decodedVarList, decodedMatrix)
      case TFFUnary(conn, body) =>
        val decodedConn = decodeTFFConnective(conn)
        val decodedBody = decodeTFFLogicFormula(body)
        THFUnary(decodedConn, decodedBody)
      case TFFInequality(left, right) =>
        import leo.datastructures.tptp.thf.{Neq => THFNeq}
        val decodeLeft = decodeTerm(left)
        val decodeRight = decodeTerm(right)
        THFBinary(decodeLeft, THFNeq, decodeRight)
      case TFFAtomic(atomicFormula) =>
        decodeAtomicFormula(atomicFormula)
      case TFFCond(cond, thn, els) =>
        val decodedCond = decodeTFFLogicFormula(cond)
        val decodedThn = decodeTFFLogicFormula(thn)
        val decodedEls = decodeTFFLogicFormula(els)
        THFCond(decodedCond, decodedThn, decodedEls)
      case TFFLet(_, _) => assert(false); null
    }
  }

  import leo.datastructures.tptp.Commons.AtomicFormula
  private def decodeAtomicFormula(formula: AtomicFormula): THFLogicFormula = {
    import leo.datastructures.tptp.Commons.{DefinedPlain, SystemPlain, Plain, Equality}
    formula match {
      case Plain(data) => decodeTerm(data)
      case DefinedPlain(data) => decodeTerm(data)
      case SystemPlain(data) => decodeTerm(data)
      case Equality(left, right) =>
        import leo.datastructures.tptp.thf.{Eq => THFEq}
        import leo.datastructures.tptp.thf.{Binary => THFBinary}
        val decodeLeft = decodeTerm(left)
        val decodeRight = decodeTerm(right)
        THFBinary(decodeLeft, THFEq, decodeRight)
    }
  }

  import leo.datastructures.tptp.Commons.Term
  private def decodeTerm(term: Term): THFLogicFormula = {
    import leo.datastructures.tptp.Commons.{Func, DefinedFunc, SystemFunc, Var, NumberTerm, Distinct}
    import leo.datastructures.tptp.thf.{Function => THFFunction, Var => THFVar,
      Distinct => THFDistinct, Number => THFNumber, App => THFApp, Binary => THFBinary}
    term match {
      case Func(f, args) =>
        val decodedArgs = args.map(decodeTerm)
        if (isApp(f)) {
          assert(args.size == 2)
          THFBinary(decodedArgs.head, THFApp, decodedArgs.tail.head)
        } else if (isBoolLift(f)) {
          assert(args.size == 1)
          decodedArgs.head
        } else {
          val fun: THFLogicFormula = THFFunction(f, Seq.empty)
          decodedArgs.foldLeft(fun){case (t, arg) => THFBinary(t, THFApp, arg)}
        }
//        THFFunction(f, decodedArgs)
      case DefinedFunc(f, args) =>
        val decodedArgs = args.map(decodeTerm)
        THFFunction(f, decodedArgs)
      case SystemFunc(f, args) =>
        val decodedArgs = args.map(decodeTerm)
        THFFunction(f, decodedArgs)
      case Var(name) => THFVar(name)
      case Distinct(data) => THFDistinct(data)
      case NumberTerm(value) => THFNumber(value)
      case _ => assert(false); null
    }
  }
  private def isApp(name: String): Boolean = {
    val escapePrefix: String = leo.modules.encoding.escapeChar.toString*2
    val appName: String = "app"
    if (name.startsWith(escapePrefix ++ appName)) true else false
  }
  private def isBoolLift(name: String): Boolean = {
    val escapePrefix: String = leo.modules.encoding.escapeChar.toString*2
    val appName: String = "hBool"
    if (name.startsWith(escapePrefix ++ appName)) true else false
  }


  import leo.datastructures.tptp.tff.{BinaryConnective => TFFBinaryConnective, UnaryConnective => TFFUnaryConnective,
  Quantifier => TFFQuantifier}
  import leo.datastructures.tptp.thf.{BinaryConnective => THFBinaryConnective, UnaryConnective => THFUnaryConnective,
  Quantifier => THFQuantifier}
  private def decodeTFFConnective(connective: TFFUnaryConnective): THFUnaryConnective = {
    import leo.datastructures.tptp.tff.{Not => TFFNot}
    import leo.datastructures.tptp.thf.{~ => THFNot}
    connective match {
      case TFFNot => THFNot
      case _ => assert(false); null
    }
  }
  private def decodeTFFConnective(connective: TFFBinaryConnective): THFBinaryConnective = {
    import leo.datastructures.tptp.tff.{<=> => TFFEquiv, Impl => TFFImpl, <= => TFFIf,
    <~> => TFFNiff, ~| => TFFNor, ~& => TFFNand, | => TFFOr, & => TFFAnd}
    import leo.datastructures.tptp.thf.{<=> => THFEquiv, Impl => THFImpl, <= => THFIf,
      <~> => THFNiff, ~| => THFNor, ~& => THFNand, | => THFOr, & => THFAnd}
    connective match {
      case TFFEquiv => THFEquiv
      case TFFImpl => THFImpl
      case TFFIf => THFIf
      case TFFNiff => THFNiff
      case TFFNor => THFNor
      case TFFNand => THFNand
      case TFFOr => THFOr
      case TFFAnd => THFAnd
    }
  }
  private def decodeTFFConnective(connective: TFFQuantifier): THFQuantifier = {
    import leo.datastructures.tptp.tff.{? => TFFExists, ! => TFFAll}
    import leo.datastructures.tptp.thf.{? => THFExists, ! => THFAll}
    connective match {
      case TFFExists => THFExists
      case TFFAll => THFAll
    }
  }

  import leo.datastructures.tptp.tff.{Type => TFFType}
  private def decodeTFFType(typ: TFFType): Option[THFLogicFormula] = {
    Some(decodeTFFType0(typ))
  }

  private def decodeTFFType0(atomicType: TFFType): THFLogicFormula = {
    import leo.datastructures.tptp.tff.{AtomicType => TFFAtomicType, * => TFFFunType, -> => TFFTopFunType}
    import leo.datastructures.tptp.thf.{-> => THFFunType, BinType => THFBinType, Function => THFFunction}
    atomicType match {
      case TFFAtomicType(name, args) =>
        if (name.startsWith(escapeChar.toString)) {
          val name0 = name.tail
          if (name0.startsWith(safeName(TypedFOLEncodingSignature.funTy_name))) {

          }
        }
        val decodedTypes = args.map(decodeTFFType0)
        THFFunction(name, decodedTypes)
      case TFFTopFunType(types) =>
        val decodedTypes = types.map(decodeTFFType0)
        THFBinType(THFFunType(decodedTypes))
      case TFFFunType(types) =>
        val decodedTypes = types.map(decodeTFFType0)
        THFBinType(THFFunType(decodedTypes))
      case _ => assert(false); null
    }
  }
  // first 'x' was already stripped
  private val funName: String = escapeChar + TypedFOLEncodingSignature.funTy_name
  private def decodeCanonicalTyName(name: String): Any = {
    if (name.startsWith(funName)) {
      val tyName = name.drop(funName.size)
      assert(tyName.head == '_')
      val tyName0 = tyName.tail
      val dom = tyName0.takeWhile(_ != '_')  // TODO: depth-first search on xfun
      val tyName1 = tyName0.dropWhile(_ != '_').tail
      ???
    } else {
      ???
    }
  }
}
