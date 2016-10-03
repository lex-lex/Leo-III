package leo.modules.normalization

import leo.modules.preprocessing.PrenexNormal
import leo.{Checked, LeoTestSuite}
import leo.datastructures._
import Term._
import HOLSignature.o

/**
 * Created by ryu on 6/17/14.
 */
class PrenexTestSuite extends LeoTestSuite {

  val s = getFreshSignature

  val skVar = mkAtom(s.freshSkolemConst(o))

  val toNorm : Map[Term,Term] = Map[Term, Term](
    (&(Forall(\(o)(mkBound(o,1))), skVar), Forall(\(o)(&(mkBound(o,1), skVar)))),
    (&(skVar,Forall(\(o)(mkBound(o,1)))), Forall(\(o)(&(skVar,mkBound(o,1))))),
    (&(Forall(\(o)(mkBound(o,1))),Forall(\(o)(mkBound(o,1)))), Forall(\(o)(Forall(\(o)(&(mkBound(o,2),mkBound(o,1)))))))
  )

//  println("\n----------------------\nPrenexNormalform Test.\n--------------------")
  for ((t,t1) <- toNorm){
//    println("('"+t.pretty+"' , '"+t1.pretty+"')")
    test("Prenex Test:"+t.pretty, Checked) {
      val st = PrenexNormal(termToClause(t)).lits.head.term
      println("Prenex: The Term '" + t.pretty + "' was normalized to '" + st.pretty + "'.")
      assert(st == t1, "\nThe negation normalized Term '" + t.pretty + "' should be '" + t1.pretty + "', but was '" + st.pretty + "'.")
    }
  }

  def termToClause(t : Term) : Clause = Clause.mkClause(List(Literal(t, true)),Derived)
}
