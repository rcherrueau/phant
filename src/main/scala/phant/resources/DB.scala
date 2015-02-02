package phant
package resources

object db {
  sealed abstract class DB {
    type This >: this.type <: DB

    type Head
    def head: Seq[Head]

    type Tail <: DB
    def tail: Tail
  }

  final case class |:[H, T <: DB](val head: Seq[H],
                                  val tail: T) extends DB {
    type Head = H
    type Tail = T
    type This = |:[Head,Tail]
  }

  final object EOCol extends DB {
    type Head = Nothing
    type Tail = Nothing
    type This = EOCol

    def head = throw new NoSuchElementException("DB.head")
    def tail = throw new NoSuchElementException("DB.tail")
  }
  type EOCol = EOCol.type

  object DB {
    def apply[T1](ts: (T1)*): |:[T1,EOCol] = |:(ts, EOCol)

    // Implicits are there to avoid apply ambiguity after type
    // erasure.
    def apply[T1,T2](ts: (T1, T2)*)(implicit
                                    $d01: DummyImplicit):
        |:[T1,|:[T2,EOCol]] = {
      val (t1s, t2s) = ts.foldLeft((Nil:List[T1],Nil:List[T2])) {
        case ((t1s, t2s), (t1, t2)) => (t1 :: t1s, t2 :: t2s)
      }

      |:(t1s, |:(t2s, EOCol))
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

      |:(t1s, |:(t2s, |:(t3s, EOCol)))
    }

    def _unsafe[T](f: => Any) = f.asInstanceOf[T]
  }
}
