package leo.modules.output

import leo.datastructures._
import Term._
import leo.datastructures.Type._
import leo.datastructures._
import leo.modules.HOLSignature.{LitFalse, |||, &, Not, Forall, Exists, TyForall, !===, ===, Impl, <=, <=>, ~&, ~|||, <~>}
import leo.modules.SZSException

import scala.annotation.tailrec

/**
  * Translation module that takes internal terms or types and translates them
  * to a TPTP representation (in THF format).
  * Translation can be done directly into a string by methods `toString`
  * or indirect into an `Output` object by the `output` method.
  *
  * @see [[Term]], [[leo.datastructures.ClauseProxy]], [[leo.modules.output.Output]]
  * @author Alexander Steen
  * @since 07.11.2014
  * @todo Merge lambda and type lambda in backward translation, can we?
  * @todo Check if ordering is important (i.e. all types before definitions), see apply[A <: ClauseProxy](formulas : Set[A]): Seq[Output]
  */
object ToTPTP {
  ///////////////////////
  // Methods on ClauseProxys
  ///////////////////////

  /** Return a textual representation of `f` in THF, i.e. returns
    * "thf(id, term, role)." where
    * `id` equals `f.cl.id`, `term` is a representation of `f.cl` as term,
    * `role` equals `f.role.pretty`. */
  final def toString(f: ClauseProxy)(implicit sig: Signature): String = toTPTP(f.id.toString, f.cl, f.role)(sig)
  /** See toString(ClauseProxy).
    * The textual representation is returned as an `Output` object. */
  final def output(f: ClauseProxy)(implicit sig: Signature): Output = new Output {
    def apply = toTPTP(f.id.toString, f.cl, f.role)(sig)
  }

  /**
    * Return a textual representation of `f` with (optional) annotation in THF, i.e. returns
    * "thf(id, term, role, annotation)." where
    * `id` equals `f.cl.id`, `term` is a representation of `f.cl` as term,
    * `role` equals `f.role.pretty`, `annotation` equals a representation of `f.annotation`. */
  final def withAnnotation(cl: ClauseProxy)(implicit sig: Signature): String = {
      //      val normclause = leo.modules.calculus.Simp(cl.cl)
      toTPTP(cl.id.toString, cl.cl, cl.role, cl.annotation)(sig)
  }
  /** See withAnnotation(ClauseProxy).
    * The textual representation is returned as an `Output` object. */
  final def outputWithAnnotation(cl: ClauseProxy)(implicit sig: Signature): Output = new Output {
    def apply = toTPTP(cl.id.toString, cl.cl, cl.role, cl.annotation)(sig)
  }

  ///////////////////////
  // Methods on other term inputs
  ///////////////////////

  /**
    * Translate the whole package: Take all constants from signature (types, uninterpreted symbols, definitions)
    * and the formulas in `formulas`. The output sequence contains first the constants from signature, then the formulas.
    */
  final def apply[A <: ClauseProxy](formulas : Set[A])(implicit sig: Signature): Seq[Output] = {
    var out: Seq[Output] = Seq()
    var defs : Seq[Output] = Seq()
    val sortsig = sig.allUserConstants.toSeq.sortBy(x => x)
    sortsig foreach { k => // Sorted by id
      out = typeToTPTPOutput(k) +: out
      definitionToTPTPOutput(k) foreach {o => println(o()); defs = o +: defs}
    }
    out = defs ++ out
    formulas foreach {formula =>
      out = ToTPTP.output(formula) +: out}
    out.reverse
  }

  ///////////////////////
  // Methods on symbols/definitions
  ///////////////////////

  final def apply(k: Signature#Key)(implicit sig: Signature): String = {
    val constant = sig.apply(k)
    val cname = if (constant.name.startsWith("'") && constant.name.endsWith("'")) {
      "'" + constant.name.substring(1, constant.name.length-1).replaceAll("\\\\", """\\\\""").replaceAll("\\'", """\\'""") + "'"
    } else {
      constant.name
    }
    if (constant.hasType) {
      // Its a term constant or a definition
      // Print out type declaration (needed in all cases)
      val tyDecl = s"thf(${cname}_type, type, $cname: ${toTPTP(constant._ty)(sig)})."
      // If its a definition, also print definition afterwards
      if (constant.hasDefn) {
        tyDecl + s"\nthf(${cname}_def, definition, ($cname = (${termToTPTP(constant._defn)(sig)})))."
      } else
        tyDecl
    } else {
      // Its a type constant
      assert(constant.hasKind)
      s"thf($cname, ${Role_Type.pretty}, $cname: ${toTPTP(constant._kind)})."
    }
  }

  final def output(k: Signature#Key)(implicit sig: Signature): Output = new Output {
    final def apply() = ToTPTP(k)(sig)
  }

  private def typeToTPTP(k: Signature#Key)(implicit sig : Signature) : String = {
    val constant = sig.apply(k)
    val cname = if (constant.name.startsWith("'") && constant.name.endsWith("'")) {
      "'" + constant.name.substring(1, constant.name.length-1).replaceAll("\\\\", """\\\\""").replaceAll("\\'", """\\'""") + "'"
    } else {
      constant.name
    }
    if (constant.hasType) {
      s"thf(${cname}_type, type, $cname: ${toTPTP(constant._ty)(sig)})."
    } else {
      // Its a type constant
      assert(constant.hasKind)
      s"thf($cname, ${Role_Type.pretty}, $cname: ${toTPTP(constant._kind)})."
    }
  }

  private def typeToTPTPOutput(k : Signature#Key)(implicit sig: Signature): Output = new Output {
    final def apply() = typeToTPTP(k)(sig)
  }

  private def definitionToTPTP(k: Signature#Key)(implicit sig : Signature) : Option[String] = {
    val constant = sig.apply(k)
    val cname = if (constant.name.startsWith("'") && constant.name.endsWith("'")) {
      "'" + constant.name.substring(1, constant.name.length - 1).replaceAll("\\\\", """\\\\""").replaceAll("\\'", """\\'""") + "'"
    } else {
      constant.name
    }
    if (constant.hasDefn) {
      Some(s"\nthf(${cname}_def, definition, ($cname = (${termToTPTP(constant._defn)(sig)}))).")
    } else {
      None
    }
  }

  private def definitionToTPTPOutput(k : Signature#Key)(implicit sig: Signature): Option[Output] =
    definitionToTPTP(k)(sig) map (x => new Output {
      final def apply() = x
    })



  ///////////////////////////////
  // Translation of other data structures
  ///////////////////////////////

  final def apply(subst: Subst, implicitlyBound: Seq[(Int, Type)])(implicit sig: Signature): Output = new Output {
    override def apply: String = {
      if (subst.length == 0) {
        ""
      } else {
        val (_,varmap) = clauseImplicitsToTPTPQuantifierList(implicitlyBound)(sig)
        val varmapMaxKey = if (varmap.nonEmpty) varmap.keySet.max else 0
        val varmapSize = varmap.size
        val sb = new StringBuilder
        var i = 1
        val max = subst.length
        while (i <= max) {
          if (varmap.keySet.contains(i)) {
            val erg = subst.substBndIdx(i)
            try {
              erg match {
                case TermFront(t) =>
                  val newVars = t.looseBounds.map(k => (k, intToName(varmapSize + k - varmapMaxKey - 1)))
                  val varmap2 = varmap ++ newVars
                  sb.append(s"bind(${varmap.apply(i)}, $$thf(${termToTPTP(t, varmap2)(sig)}))")
                case BoundFront(j) => sb.append(s"bind(${varmap.apply(i)}, $$thf(${intToName(varmapSize + j - varmapMaxKey - 1)}))")
                case _ => throw new SZSException(SZS_Error, "Types in term substitution")
              }
            } catch {
              case e: Exception => leo.Out.warn(s"Could not translate substitution entry to TPTP format, Exception raised:\n${e.toString}")
                sb.append(s"bind($i, $$thf(${erg.pretty}))")
            }
            sb.append(",")
          }
          i = i + 1
        }
        sb.init.toString()
      }
    }
  }

  ///////////////////////////////
  // Translation of clause to THF formula
  ///////////////////////////////
  final private def toTPTP(name: String, cl: Clause, role: Role, clauseAnnotation: ClauseAnnotation = null)(sig: Signature): String = {
    val sb = new StringBuffer()
    if (cl.implicitlyBound.nonEmpty) {
      // make universal quantification and then print term
      val (prefix, bVarMap) = clauseImplicitsToTPTPQuantifierList(cl.implicitlyBound)(sig)
      sb.append(s"! [$prefix]: (")
      sb.append(clauseToTPTP(cl, bVarMap)(sig))
      sb.append(")")
    } else {
      // only print term
      sb.append(clauseToTPTP(cl, Map())(sig))
    }

    // Output whole tptp thf statement
    if (clauseAnnotation == null)
      s"thf($name,${role.pretty},(${sb.toString}))."
    else {
      if (clauseAnnotation == ClauseAnnotation.NoAnnotation)
        s"thf($name,${role.pretty},(${sb.toString}))."
      else
        s"thf($name,${role.pretty},(${sb.toString}),${clauseAnnotation.pretty})."
    }
  }

  final private def clauseToTPTP(cl: Clause, bVarMap: Map[Int, String])(sig: Signature): String = {
    val sb = new StringBuilder
    if (cl.lits.isEmpty) {
      sb.append(termToTPTP(LitFalse)(sig))
    } else {
      val litIt = cl.lits.iterator
      while (litIt.hasNext) {
        val lit = litIt.next()
        if (lit.equational) {
          val (left,right) = (lit.left, lit.right)
          if (lit.polarity)
            left match {
              case Bound(_,_) | Symbol(_) => right match {
                case Bound(_,_) | Symbol(_) => sb.append(s"(${termToTPTP(left,bVarMap)(sig)} = ${termToTPTP(right,bVarMap)(sig)})")
                case _ => sb.append(s"(${termToTPTP(left,bVarMap)(sig)} = (${termToTPTP(right,bVarMap)(sig)}))")
              }
              case _ => right match {
                case Bound(_,_) | Symbol(_) => sb.append(s"((${termToTPTP(left,bVarMap)(sig)}) = ${termToTPTP(right,bVarMap)(sig)})")
                case _ => sb.append(s"((${termToTPTP(left,bVarMap)(sig)}) = (${termToTPTP(right,bVarMap)(sig)}))")
              }
            }
          else
            left match {
              case Bound(_,_) | Symbol(_) => right match {
                case Bound(_,_) | Symbol(_) => sb.append(s"(${termToTPTP(left,bVarMap)(sig)} != ${termToTPTP(right,bVarMap)(sig)})")
                case _ => sb.append(s"(${termToTPTP(left,bVarMap)(sig)} != (${termToTPTP(right,bVarMap)(sig)}))")
              }
              case _ => right match {
                case Bound(_,_) | Symbol(_) => sb.append(s"((${termToTPTP(left,bVarMap)(sig)}) != ${termToTPTP(right,bVarMap)(sig)})")
                case _ => sb.append(s"((${termToTPTP(left,bVarMap)(sig)}) != (${termToTPTP(right,bVarMap)(sig)}))")
              }
            }
        } else {
          val term = lit.left
          term match {
            case Bound(_,_) | Symbol(_) => if (lit.polarity)
                sb.append(termToTPTP(term,bVarMap)(sig))
              else
                sb.append(s"${sig(Not.key).name} (${termToTPTP(term, bVarMap)(sig)})")
            case _ => if (lit.polarity)
                sb.append(s"(${termToTPTP(term,bVarMap)(sig)})")
              else
                sb.append(s"(${sig(Not.key).name} (${termToTPTP(term, bVarMap)(sig)}))")
          }

        }
        if (litIt.hasNext) sb.append(" | ")
      }
    }
    sb.toString()
  }

  final def termToTPTP(t: Term, bVars: Map[Int,String] = Map())(sig: Signature): String = {
    t match {
      // Constant symbols
      case Symbol(id) => val name = sig(id).name
        if (name.startsWith("'") && name.endsWith("'")) {
          "'" + name.substring(1, name.length-1).replaceAll("\\\\", """\\\\""").replaceAll("\\'", """\\'""") + "'"
        } else {
          name
        }
      // Give Bound variables names
      case Bound(ty, scope) => bVars(scope)
      // Unary connectives
      case Not(t2) => s"${sig(Not.key).name} (${termToTPTP(t2, bVars)(sig)})"
      case Forall(_) => val (bVarTys, body) = collectForall(t)
                        val newBVars = makeBVarList(bVarTys, bVars.size)
        body match {
          case Forall(_) | Exists(_) | Not(_) => s"${sig(Forall.key).name} [${newBVars.map({case (s,ty) => s"$s:${toTPTP(ty)(sig)}"}).mkString(",")}]: ${termToTPTP(body, fusebVarListwithMap(newBVars, bVars))(sig)}"
          case _ => s"${sig(Forall.key).name} [${newBVars.map({case (s,ty) => s"$s:${toTPTP(ty)(sig)}"}).mkString(",")}]: (${termToTPTP(body, fusebVarListwithMap(newBVars, bVars))(sig)})"
        }

      case Exists(_) => val (bVarTys, body) = collectExists(t)
                        val newBVars = makeBVarList(bVarTys, bVars.size)
        body match {
          case Forall(_) | Exists(_) | Not(_) => s"${sig(Exists.key).name} [${newBVars.map({case (s,ty) => s"$s:${toTPTP(ty)(sig)}"}).mkString(",")}]: ${termToTPTP(body, fusebVarListwithMap(newBVars, bVars))(sig)}"
          case _ => s"${sig(Exists.key).name} [${newBVars.map({case (s,ty) => s"$s:${toTPTP(ty)(sig)}"}).mkString(",")}]: (${termToTPTP(body, fusebVarListwithMap(newBVars, bVars))(sig)})"
        }
      case TyForall(_) => val (tyAbsCount, body) = collectTyForall(t)
        s"! [${(1 to tyAbsCount).map(i => "T" + intToName(i - 1) + ": $tType").mkString(",")}]: (${termToTPTP(body, bVars)(sig)})"
      // Binary connectives
      case t1 ||| t2 => t1 match {
        case _ ||| _| Not(_) | Forall(_) | Exists(_) => t2 match {
          case _ ||| _ | Not(_) | Forall(_) | Exists(_) => s"${termToTPTP(t1, bVars)(sig)} ${sig(|||.key).name} ${termToTPTP(t2, bVars)(sig)}"
          case _ => s"${termToTPTP(t1, bVars)(sig)} ${sig(|||.key).name} (${termToTPTP(t2, bVars)(sig)})"
        }
        case _ => t2 match {
          case _ ||| _ | Not(_) | Forall(_) | Exists(_) => s"(${termToTPTP(t1, bVars)(sig)}) ${sig(|||.key).name} ${termToTPTP(t2, bVars)(sig)}"
          case _ => s"(${termToTPTP(t1, bVars)(sig)}) ${sig(|||.key).name} (${termToTPTP(t2, bVars)(sig)})"
        }
      }
      case t1 & t2 => t1 match {
        case _ & _| Not(_) | Forall(_) | Exists(_) => t2 match {
          case _ & _ | Not(_) | Forall(_) | Exists(_) => s"${termToTPTP(t1, bVars)(sig)} ${sig(&.key).name} ${termToTPTP(t2, bVars)(sig)}"
          case _ => s"${termToTPTP(t1, bVars)(sig)} ${sig(&.key).name} (${termToTPTP(t2, bVars)(sig)})"
        }
        case _ => t2 match {
          case _ & _ | Not(_) | Forall(_) | Exists(_) => s"(${termToTPTP(t1, bVars)(sig)}) ${sig(&.key).name} ${termToTPTP(t2, bVars)(sig)}"
          case _ => s"(${termToTPTP(t1, bVars)(sig)}) ${sig(&.key).name} (${termToTPTP(t2, bVars)(sig)})"
        }
      }
      case left === right => left match {
        case Bound(_,_) | Symbol(_) => right match {
          case Bound(_,_) | Symbol(_) => s"${termToTPTP(left,bVars)(sig)} ${sig(===.key).name} ${termToTPTP(right,bVars)(sig)}"
          case _ => s"${termToTPTP(left,bVars)(sig)} ${sig(===.key).name} (${termToTPTP(right,bVars)(sig)})"
        }
        case _ => right match {
          case Bound(_,_) | Symbol(_) => s"(${termToTPTP(left,bVars)(sig)}) ${sig(===.key).name} ${termToTPTP(right,bVars)(sig)}"
          case _ => s"(${termToTPTP(left,bVars)(sig)}) ${sig(===.key).name} (${termToTPTP(right,bVars)(sig)})"
        }
      }
      case left !=== right => left match {
        case Bound(_,_) | Symbol(_) => right match {
          case Bound(_,_) | Symbol(_) => s"${termToTPTP(left,bVars)(sig)} ${sig(!===.key).name} ${termToTPTP(right,bVars)(sig)}"
          case _ => s"${termToTPTP(left,bVars)(sig)} ${sig(!===.key).name} (${termToTPTP(right,bVars)(sig)})"
        }
        case _ => right match {
          case Bound(_,_) | Symbol(_) => s"(${termToTPTP(left,bVars)(sig)}) ${sig(!===.key).name} ${termToTPTP(right,bVars)(sig)}"
          case _ => s"(${termToTPTP(left,bVars)(sig)}) ${sig(!===.key).name} (${termToTPTP(right,bVars)(sig)})"
        }
      }
      case t1 Impl t2 => s"(${termToTPTP(t1, bVars)(sig)}) ${sig(Impl.key).name} (${termToTPTP(t2, bVars)(sig)})"
      case t1 <= t2  => s"(${termToTPTP(t1, bVars)(sig)}) ${sig(<=.key).name} (${termToTPTP(t2, bVars)(sig)})"
      case t1 <=> t2 => s"(${termToTPTP(t1, bVars)(sig)}) ${sig(<=>.key).name} (${termToTPTP(t2, bVars)(sig)})"
      case t1 ~& t2 => s"(${termToTPTP(t1, bVars)(sig)}) ${sig(~&.key).name} (${termToTPTP(t2, bVars)(sig)})"
      case t1 ~||| t2 => s"(${termToTPTP(t1, bVars)(sig)}) ${sig(~|||.key).name} (${termToTPTP(t2, bVars)(sig)})"
      case t1 <~> t2 => s"(${termToTPTP(t1, bVars)(sig)}) ${sig(<~>.key).name} (${termToTPTP(t2, bVars)(sig)})"
      // General structure
      case _ :::> _ => val (bVarTys, body) = collectLambdas(t)
                       val newBVars = makeBVarList(bVarTys, bVars.size)
        body match {
          case Forall(_) | Exists(_) | Not(_) => s"^ [${newBVars.map({case (s,ty) => s"$s:${toTPTP(ty)(sig)}"}).mkString(",")}]: ${termToTPTP(body, fusebVarListwithMap(newBVars, bVars))(sig)}"
          case _ => s"^ [${newBVars.map({case (s,ty) => s"$s:${toTPTP(ty)(sig)}"}).mkString(",")}]: (${termToTPTP(body, fusebVarListwithMap(newBVars, bVars))(sig)})"
        }
      case TypeLambda(_) => val (tyAbsCount, body) = collectTyLambdas(0, t)
        s"^ [${(1 to tyAbsCount).map(i => "T" + intToName(i - 1) + ": $tType").mkString(",")}]: (${termToTPTP(body, bVars)(sig)})"
      case f ∙ args => args.foldLeft(termToTPTP(f, bVars)(sig))({case (str, arg) => s"$str @ ${arg.fold(
        //Translate terms as arguments
        {
          case termArg@(Bound(_,_) | Symbol(_)) => termToTPTP(termArg, bVars)(sig)
          case termArg => "("+termToTPTP(termArg, bVars)(sig)+")"
        },
        //Translate types as arguments
        tyArg =>
          "("+toTPTP0(tyArg)(sig)+")"
      )}"})
      // Others should be invalid
      case _ => throw new IllegalArgumentException("Unexpected term format during toTPTP conversion")
    }
  }

  ///////////////////////////////
  // Translation of THF types
  ///////////////////////////////


  final private def toTPTP(ty: Type)(sig: Signature): String = ty match {
    case ∀(t) => val (tyAbsCount, bodyTy) = collectForallTys(0, ty)
      "!>[" + (1 to tyAbsCount).map(i => "T" + intToName(i - 1) + ": $tType").mkString(",") + "]: " + toTPTP0(bodyTy)(sig)
    case _ => toTPTP0(ty)(sig)
  }
  final private def toTPTP0(ty: Type)(sig: Signature): String = ty match {
    case BaseType(id) => sig(id).name
    case ComposedType(id, args) => s"${sig(id).name} @ ${args.map(toTPTP0(_)(sig)).mkString(" @ ")}"
    case BoundType(scope) => "T" + intToName(scope- 1)
    case t1 -> t2 => s"(${toTPTP(t1)(sig)} > ${toTPTP(t2)(sig)})"
    case t1 * t2 => s"(${toTPTP(t1)(sig)} * ${toTPTP(t2)(sig)})"
    case t1 + t2 => s"(${toTPTP(t1)(sig)} + ${toTPTP(t2)(sig)})"
    case ∀(t) => throw new IllegalArgumentException("Polytype should have been caught before")
    /**s"${Signature.get(Forall.key).name} []: ${toTPTP(t)}"*/
  }

  final private def toTPTP(k: Kind): String = {
    import leo.datastructures.Kind.->
    k match {
      case Kind.typeKind => "$tType"
      case k1 -> k2 => if (k1.isTypeKind)
        s"$$tType > ${toTPTP(k2)}"
      else
        s"(${toTPTP(k1)}) > ${toTPTP(k2)}"
    }
  }

  ///////////////////////////////
  // Utility methods
  ///////////////////////////////
  // Term quantification collection
  /** Gather consecutive all-quantifications (nameless). */
  final private def collectForall(t: Term): (Seq[Type], Term) = {
    collectForall0(Seq.empty, t)
  }
  @tailrec
  @inline final private def collectForall0(vars: Seq[Type], t: Term): (Seq[Type], Term) = {
    t match {
      case Forall(ty :::> b) => collectForall0(vars :+ ty, b)
      case Forall(_) => throw new IllegalArgumentException("Unexcepted body term in all quantification decomposition.")
      case _ => (vars, t)
    }
  }

  /** Gather consecutive all-type-quantifications (nameless). */
  final private def collectTyForall(t: Term): (Int, Term) = {
    collectTyForall0(0, t)
  }
  @tailrec
  @inline final private def collectTyForall0(vars: Int, t: Term): (Int, Term) = {
    t match {
      case TyForall(TypeLambda(body)) => collectTyForall0(vars +1, body)
      case TyForall(_) => throw new IllegalArgumentException("Unexcepted body term in type-forall quantification decomposition.")
      case _ => (vars, t)
    }
  }


  /** Gather consecutive exist-quantifications (nameless). */
  final private def collectExists(t: Term): (Seq[Type], Term) = {
    collectExists0(Seq.empty, t)
  }
  @tailrec
  @inline final private def collectExists0(vars: Seq[Type], t: Term): (Seq[Type], Term) = {
    t match {
      case Exists(ty :::> b) => collectExists0(vars :+ ty, b)
      case Exists(_) => throw new IllegalArgumentException("Unexcepted body term in existsl quantification decomposition.")
      case _ => (vars, t)
    }
  }

  /** Gather consecutive lambda-abstractions (nameless).
    * Returns [t1, t2, ..., tn] where t1 is the outermost type */
  final private def collectLambdas(t: Term): (Seq[Type], Term) = {
    collectLambdas0(Seq.empty, t)
  }
  @tailrec
  @inline final private def collectLambdas0(vars: Seq[Type], t: Term): (Seq[Type], Term) = {
    t match {
      case ty :::> b => collectLambdas0(vars :+ ty, b)
      case _ => (vars, t)
    }
  }

  @tailrec
  private final def collectTyLambdas(count: Int, t: Term): (Int, Term) = {
    t match {
      case TypeLambda(body) => collectTyLambdas(count+1, body)
      case _ => (count, t)
    }
  }

  // Type quantification collection
  @tailrec
  private final def collectForallTys(count: Int, ty: Type): (Int, Type) = {
    ty match {
      case ∀(t) => collectForallTys(count+1, t)
      case _ => (count, ty)
    }
  }


  private final def makeBVarList(tys: Seq[Type], offset: Int): Seq[(String, Type)] = {
    tys.zipWithIndex.map {case (ty, idx) => (intToName(offset + idx), ty)}
  }
  private final def fusebVarListwithMap(bvarList: Seq[(String, Type)], oldbvarMap: Map[Int,String]): Map[Int, String] = {
    val newVarCount = bvarList.size
    val newVarsAsKeyValueList = bvarList.zipWithIndex.map {case ((name, ty),idx) => (newVarCount - idx, name)}
    oldbvarMap.map {case (k,v) => (k+newVarCount, v)} ++ Map(newVarsAsKeyValueList:_*)
  }

  final private def clauseImplicitsToTPTPQuantifierList(implicitlyQuantified: Seq[(Int, Type)])(sig: Signature): (String, Map[Int, String]) = {
    val count = implicitlyQuantified.size
    var sb: Seq[String] = Seq()
    var resultBindingMap: Map[Int, String] = Map()

    var curImplicitlyQuantified = implicitlyQuantified
    var i = 0
    while(i < count) {
      val (scope,ty) = curImplicitlyQuantified.head
      curImplicitlyQuantified = curImplicitlyQuantified.tail
      val name = intToName(count - i - 1)
      sb = s"$name: ${toTPTP(ty)(sig)}" +: sb
      resultBindingMap = resultBindingMap + (scope -> name)
      i = i + 1
    }
    (sb.mkString(","), resultBindingMap)
  }


  ///////////////////////////////
  // Naming of variables
  ///////////////////////////////

  @inline final private val asciiA = 65
  @inline final private val asciiZ = 90
  @inline final private val range = asciiZ - asciiA // range 0,1,....

  /**
    * Convert index i (variable in de-bruijn format) to a variable name corresponding to ASCII transformation as follows:
    * 0 ---> "A",
    * 1 ---> "B",
    * 25 ---> "Z",
    * 26 ---> "ZA", ... etc.
    */
  final private def intToName(i: Int): String = i match {
    case n if n <= range => s"${intToChar(i)}"
    case n if n > range => s"Z${intToName(i-range-1)}"
  }
  final private def intToChar(i: Int): Char = i match {
    case n if n <= range => (n + asciiA).toChar
    case _ => throw new IllegalArgumentException
  }
}
