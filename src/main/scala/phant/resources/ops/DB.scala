package phant
package resources
package ops

object db {
  import shapeless._

  /** Type class selects first `n` columns. */
  trait Taker[N <: Nat, Db <: DB] {
    type Out <: DB

    def take(db: Db): Out
  }

  object Taker {
    def apply[N <: Nat, Db <: DB](db: Db)(implicit
                                          taker: Taker[N,Db]):
        taker.Out = taker.take(db)

    implicit def ZeroTake[Db <: DB] = new Taker[_0, Db] {
      type Out = EOCol
      def take(db: Db) = EOCol
    }

    implicit def SuccTaker[N <: Nat, Db <: DB](implicit
                                               taker: Taker[N, Db#Tail]) =
      new Taker[Succ[N], Db] {
        type Out = |:[Db#Head, taker.Out]
        def take(db: Db) = |:(db.head, taker.take(db.tail))
      }
  }

  /** Type class selects all coliumns except first `n` ones. */
  trait Dpper[N <: Nat, Db <: DB] {
    type Out <: DB
    def drop(db: Db): Out
  }

  object Dpper {
    def apply[N <: Nat, Db <: DB](db: Db)(implicit
                                          dpper: Dpper[N,Db]) =
      dpper.drop(db)

    implicit def ZeroDpper[Db <: DB] = new Dpper[_0, Db] {
      type Out = Db
      def drop(db: Db) = db
    }

    implicit def SuccDpper[N <: Nat, Db <: DB](implicit
                                               dpper: Dpper[N, Db#Tail]) =
      new Dpper[Succ[N], Db] {
        type Out = dpper.Out
        def drop(db: Db) = dpper.drop(db.tail)
    }
  }

  /** Type class splits at `n` column. */
  object Splitter {
    def apply[N <: Nat, Db <: DB](db: Db)(implicit
                                          taker: Taker[N,Db],
                                          dpper: Dpper[N,Db]) =
      (Taker(db), Dpper(db))
  }

  object TakerV {
    def apply[Db <: DB](n: Int, db: Db): Db#This = DB._unsafe[Db#This](
      db match {
        case |:(h, t) => |:(h.take(n), TakerV(n, t))
        case _ => EOCol
      })
  }

  object DpperV {
    def apply[Db <: DB](n: Int, db: Db): Db#This = DB._unsafe[Db#This](
      db match {
        case |:(h, t) => |:(h.drop(n), DpperV(n, t))
        case _ => EOCol
      })
  }

  object SplitterV {
    def apply[Db <: DB](n: Int, db: Db) =
      (TakerV(n, db), DpperV(n, db))
  }
}
