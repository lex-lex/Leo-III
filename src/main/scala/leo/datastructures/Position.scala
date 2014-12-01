package leo.datastructures

/**
 * Created by lex on 16.10.14.
 */
abstract class Position(protected val seq: Seq[Int]) {
  import leo.datastructures.Position.DerivedPos

  def posHead: Int = seq.head
  def tail: Position = DerivedPos(seq.tail)

  def abstrPos: Position = new DerivedPos(seq :+ 1)
  def headPos: Position = new DerivedPos(seq :+ 1)
  def spinePos: Position = new DerivedPos(seq :+ 2)
  def argPos(i: Int): Position = new DerivedPos(seq :+ i)


  def prependAbstrPos: Position = new DerivedPos(1 +: seq)
  def prependHeadPos: Position = new DerivedPos(1 +: seq)
  def prependSpinePos: Position = new DerivedPos(2 +: seq)
  def preprendArgPos(i: Int): Position = new DerivedPos(i +: seq)
}


object Position {
  def root: Position = RootPos

  protected case class DerivedPos(pos: Seq[Int]) extends Position(pos)
  protected case object RootPos extends Position(Seq.empty)

  object AbstrPos {
    def unapply(pos: Position): Boolean = {
      pos.seq.nonEmpty && pos.seq.head == 1
    }
  }

  object HeadPos {
    def unapply(pos: Position): Boolean = {
      pos.seq.nonEmpty && pos.seq.head == 1
    }
  }

  object SpinePos {
    def unapply(pos: Position): Boolean = {
      pos.seq.nonEmpty && pos.seq.head == 2
    }
  }

  object ArgsPos {
    def unapply(pos: Position): Boolean = {
      pos.seq.nonEmpty
    }
  }
}