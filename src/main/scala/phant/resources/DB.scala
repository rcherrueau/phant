package phant
package resources

sealed abstract class DB {
  type This >: this.type <: DB

  type Head
  def head: Seq[Head]

  type Tail <: DB
  def tail: Tail

  def isEmpty: Boolean = head.isEmpty
  def lines: Int = head.length
}

final case class |:[H, T <: DB](val head: Seq[H],
                                val tail: T) extends DB {
  type Head = H
  type Tail = T
  type This = |:[Head,Tail]

  override def toString = head + " |:\n" + tail + ""
  override def equals(o: Any): Boolean = o match {
    case |:(h, t) => head == h
    case _ => false
  }
}

trait EOCol extends DB {
  type Head = Nothing
  type Tail = Nothing
  type This = EOCol

  def head = throw new NoSuchElementException("DB.head")
  def tail = throw new NoSuchElementException("DB.tail")
  override def isEmpty = true
  override def lines = throw new NoSuchElementException("DB.lines")

  override def toString = "EOCol"
  override def equals(o: Any): Boolean = o match {
    case Nil => true
    case _ => false
  }
}
final object EOCol extends EOCol

object DB {
  def apply(): EOCol = EOCol

  def apply[T1](ts: (T1)*): |:[T1,EOCol] = |:(ts.toList, EOCol)

  // Implicits are there to avoid apply ambiguity after type
  // erasure.
  def apply[T1,T2](ts: (T1, T2)*)(implicit
                                  $d01: DummyImplicit):
      |:[T1,|:[T2,EOCol]] = {
    val (t1s, t2s) = ts.foldLeft((Nil:List[T1],Nil:List[T2])) {
      case ((t1s, t2s), (t1, t2)) => (t1 :: t1s, t2 :: t2s)
    }

    |:(t1s.reverse, |:(t2s.reverse, EOCol))
  }

  def apply[T1,T2,T3](ts: (T1,T2,T3)*)(implicit
                                       $d01: DummyImplicit,
                                       $d02: DummyImplicit):
      |:[T1,|:[T2,|:[T3,EOCol]]] = {
    val (t1s, t2s, t3s) =
      ts.foldLeft((Nil:List[T1],Nil:List[T2],Nil:List[T3])) {
        case ((t1s, t2s, t3s), (t1, t2, t3)) =>
          (t1 :: t1s, t2 :: t2s, t3 :: t3s)
      }

    |:(t1s.reverse, |:(t2s.reverse, |:(t3s.reverse, EOCol)))
  }

  // Convert this DB into DBOps: "pimp-my-library" pattern
  import syntax.DBOps
  import scala.language.implicitConversions
  implicit def db2dbOps[Db <: DB](db: Db): DBOps[Db] =
    new DBOps(db)

  def _unsafe[T](f: => Any) = f.asInstanceOf[T]
}
