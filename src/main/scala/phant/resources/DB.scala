package phant
package resources
object db {

  trait TypedFunction2[-T1, -T2, +R,
                       F[_ <: T1, _ <: T2] <: R] {
    def apply[P1 <: T1, P2 <: T2](p1: P1, p2: P2): F[P1, P2]
  }

  import nat._

  sealed abstract class DB {
    type This >: this.type <: DB

    type Head
    def head: Seq[Head]

    type Tail <: DB
    def tail: Tail

    type Fold[U, F[_, _ <: U] <: U, Z <: U] <: U
    def fold[U, F[_, _ <: U] <: U, Z <: U]
      (f: TypedFunction2[Any, U, U, F], z: Z): Fold[U, F, Z]

    type Take[N <: Nat] <: DB
    def take[N <: Nat](n: N): Take[N] = DB._unsafe[Take[N]](this match {
      case _ if (n.value <= 0) => EOCol
      case EOCol => EOCol
      case |:(h, t) => |:(h, t.take(n --))
    })

    type Drop[N <: Nat] <: DB
    def drop[N <: Nat](n: N): Drop[N] = DB._unsafe[Drop[N]](this match {
      case _ if (n.value <= 0) => this
      case EOCol => EOCol
      case |:(h, t) => t.drop(n --)
    })

    type Split[N <: Nat] = (Take[N], Drop[N])
    def split[N <: Nat](n: N): Split[N] = (take(n), drop(n))

//    type Length = Fold[Nat, ({ type λ[_, N <: Nat] = N # ++ })#λ, Zero]
    def length =
      fold[Nat, ({ type λ[_, N <: Nat] = N # ++ })#λ, Zero](
        new TypedFunction2[Any, Nat, Nat,
                           ({ type λ[_, N <: Nat] = N # ++ })#λ] {
          def apply[P1 <: Any, P2 <: Nat](p1: P1, p2: P2) = {
            println("here " + p2.value)
            p2 ++
          }
        }, Zero)

    def takeV(n: Int): This = DB._unsafe[This](this match {
      case |:(h, t) => |:(h.take(n), t.takeV(n))
      case EOCol => EOCol
    })

    def dropV(n: Int): This = DB._unsafe[This](this match {
      case |:(h, t) => |:(h.drop(n), t.dropV(n))
      case EOCol => EOCol
    })

    def splitV(n: Int) = (takeV(n), dropV(n))

    def lengthV: Int = head.length

    // TODO: map, flatMap, filter
  }

  final case class |:[H, T <: DB](val head: Seq[H],
                                  val tail: T) extends DB {
    type Head = H
    type Tail = T
    type This = |:[Head,Tail]

    override type Take[N <: Nat] = N # LTEq_0[DB,
                                              EOCol,
                                              |:[Head, Tail # Take[N # --]]]

    override type Drop[N <: Nat] = N # LTEq_0[DB,
                                              This,
                                              Tail # Drop[N # --]]

    override type Fold[U, F[_, _ <: U] <: U, Z <: U] = F[Seq[Head], Tail#Fold[U, F, Z]]
    override def fold[U, F[_, _ <: U] <: U, Z <: U]
      (f: TypedFunction2[Any, U, U, F], z: Z): Fold[U, F, Z] =
        f.apply[Seq[Head], T#Fold[U, F, Z]](head, tail.fold[U, F, Z](f, z))
  }

  final object EOCol extends DB {
    type Head = Nothing
    type Tail = Nothing
    type This = EOCol

    def head = throw new NoSuchElementException("DB.head")
    def tail = throw new NoSuchElementException("DB.tail")

    override type Take[N <: Nat] = EOCol
    override type Drop[N <: Nat] = EOCol

    override type Fold[U, F[_, _ <: U] <: U, Z <: U] = Z
    override def fold[U, F[_, _ <: U] <: U, Z <: U]
      (f: TypedFunction2[Any, U, U, F], z: Z) = z
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
