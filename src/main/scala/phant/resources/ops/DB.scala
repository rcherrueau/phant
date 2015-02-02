package phant
package resources
package ops

object db {
  //  import nat._
  import resources.db.DB
  import resources.db.|:
  import resources.db.EOCol

  trait Nat
  case class Zero() extends Nat
  case class Succ[N <: Nat](x: N) extends Nat

  /** Type class selects first `n` columns. */
  trait Taker[N <: Nat, Db <: DB] {
    type Out <: DB

    def take(n: N, db: Db): Out
  }

  object Taker {
    def apply[N <: Nat, Db <: DB](n: N, db: Db)(implicit
                                               taker: Taker[N,Db]):
        taker.Out = taker.take(n, db)

    implicit def ZeroTake[Db <: DB] = new Taker[Zero, Db] {
      type Out = EOCol
      def take(n: Zero, db: Db) = EOCol
    }

    implicit def SuccTaker[N <: Nat, Db <: DB](implicit
                                               taker: Taker[N, Db#Tail]) =
      new Taker[Succ[N], Db] {
        type Out = |:[Db#Head, taker.Out]
        def take(n: Succ[N], db: Db) = n match {
          case Succ(i) => |:(db.head, taker.take(i, db.tail))
        }
      }
  }

  /** Type class selects all coliumns except first `n` ones. */
  trait Dpper[N <: Nat, Db <: DB] {
    type Out <: DB
    def drop(n: N, db: Db): Out
  }

  object Dpper {
    def apply[N <: Nat, Db <: DB](n: N, db: Db)(implicit
                                                dpper: Dpper[N,Db]) =
      dpper.drop(n, db)

    implicit def ZeroDpper[Db <: DB] = new Dpper[Zero, Db] {
      type Out = Db
      def drop(n: Zero, db: Db) = db
    }

    implicit def SuccDpper[N <: Nat, Db <: DB](implicit
                                               dpper: Dpper[N, Db#Tail]) =
      new Dpper[Succ[N], Db] {
        type Out = dpper.Out
        def drop(n: Succ[N], db: Db) = n match {
          case Succ(i) => dpper.drop(i, db.tail)
        }
    }
  }

  /** Type class splits at `n` column. */
  object Splitter {
    def apply[N <: Nat, Db <: DB](n: N, db: Db)(implicit
                                                taker: Taker[N,Db],
                                                dpper: Dpper[N,Db]) =
      (Taker(n, db), Dpper(n, db))
  }

  /** Type class selects first `n` lines. */
  trait TakerV[Db <: DB] {
    type Out <: DB
    def take(n: Int, db: Db): Out
  }

  object TakerV {
    def apply[Db <: DB](n: Int, db: Db)(implicit
                                        takerv: TakerV[Db]) =
      takerv.take(n, db)

    implicit def EOColTakerV = new TakerV[EOCol] {
      type Out = EOCol
      def take(n: Int, db: EOCol) = EOCol
    }

    implicit def ConsTakerV[Db <: DB](implicit
                                      takerv: TakerV[Db#Tail]) =
      new TakerV[Db] {
        type Out = |:[Db#Head, takerv.Out]
        def take(n: Int, db: Db) =
          |:(db.head.take(n), takerv.take(n, db.tail))
      }
  }

  /** Type class selects all lignes except first `n` ones. */
  trait DpperV[Db <: DB] {
    type Out <: DB
    def drop(n: Int, db: Db): Out
  }

  object DpperV {
    def apply[Db <: DB](n: Int, db: Db)(implicit
                                        dpperv: DpperV[Db]) =
      dpperv.drop(n, db)

    implicit def EOColDpperV = new DpperV[EOCol] {
      type Out = EOCol
      def drop(n: Int, db: EOCol) = EOCol
    }

    implicit def ConsDpperV[Db <: DB](implicit
                                      dpperv: DpperV[Db#Tail]) =
      new DpperV[Db] {
        type Out = |:[Db#Head, dpperv.Out]
        def drop(n: Int, db: Db) =
          |:(db.head.drop(n), dpperv.drop(n, db.tail))
      }
  }

  object SplitterV {
    def apply[Db <: DB](n: Int, db: Db)(implicit
                                        takerv: TakerV[Db],
                                        dpperv: DpperV[Db]) =
      (takerv.take(n, db), dpperv.drop(n, db))
  }
}
