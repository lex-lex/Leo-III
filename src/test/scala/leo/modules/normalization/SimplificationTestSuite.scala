package leo.modules.normalization

import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import leo.datastructures.internal._
import scala.collection.immutable.HashMap
import leo.datastructures.internal.Term._
import org.scalatest.FunSuite

/**
 * Created by Max Wisniewski on 6/10/14.
 */
@RunWith(classOf[JUnitRunner])
class SimplificationTestSuite extends FunSuite {
  val s = Signature.get

  val p = mkAtom(s.addUninterpreted("p",s.o))
  val q = mkAtom(s.addUninterpreted("q", s.o))

  val toSimpl : Map[Term,Term] = Map[Term, Term](
    (Not(LitTrue()),LitFalse()),
    (Not(LitFalse()), LitTrue()),
    (&(p,p),p),
    (&(p,Not(p)), LitFalse()),
    (<=>(p,p), LitTrue()),
    (&(p,LitTrue()), p),
    (&(p,LitFalse()), LitFalse()),
    (Impl(p,LitTrue()), LitTrue()),
    (Impl(p,LitFalse()), Not(p)),
    (<=>(p,LitTrue()), p),
    (<=>(p,LitFalse()), Not(p)),
    (|||(p,p), p),
    (|||(p,Not(p)), LitTrue()),
    (Impl(p,p), LitTrue()),
    (|||(p,LitTrue()), LitTrue()),
    (|||(p,LitFalse()), p),
    (Impl(LitTrue(), p), p),
    (Impl(LitFalse(), p), LitTrue()),
    (Forall(mkTermAbs(s.o,p)),p),
    (Exists(mkTermAbs(s.o, p)),p),
    (Forall(mkTermAbs(s.o, <=>(mkTermApp(p, mkBound(s.o,1)), mkTermApp(p, mkBound(s.o,1))))), LitTrue())
  )

//  println("\n-------------------\nSimplification Test.\n---------------------------")
  for ((t,t1) <- toSimpl){
    test("Simplification Test: "+t.pretty) {
      val st = Simplification(t, 0)
      println("Simplicifcation: '" + t.pretty + "' was simplified to '" + st.pretty)
      assert(st == t1, "\nThe simplified Term '" + t.pretty + "' should be '" + t1.pretty + "', but was '" + st.pretty + "'.")
    }
  }
}