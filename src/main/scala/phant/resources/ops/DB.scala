package phant
package resources
package ops

object db {
  import shapeless.Nat, shapeless.Succ, Nat._

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
  trait Dropper[N <: Nat, Db <: DB] {
    type Out <: DB
    def drop(db: Db): Out
  }

  object Dropper {
    def apply[N <: Nat, Db <: DB](db: Db)(implicit
                                          dpper: Dropper[N,Db]) =
      dpper.drop(db)

    implicit def ZeroDropper[Db <: DB] = new Dropper[_0, Db] {
      type Out = Db
      def drop(db: Db) = db
    }

    implicit def SuccDropper[N <: Nat, Db <: DB](implicit
                                                 dpper: Dropper[N, Db#Tail]) =
      new Dropper[Succ[N], Db] {
        type Out = dpper.Out
        def drop(db: Db) = dpper.drop(db.tail)
    }
  }

  /** Type class splits at `n` column. */
  trait Splitter[N <: Nat, Db <: DB] {
    type Prefix <: DB
    type Suffix <: DB
    type Out = (Prefix, Suffix)
    def split(db: Db): Out
  }

  object Splitter {
    def apply[N <: Nat, Db <: DB](db: Db)(implicit
                                          spter: Splitter[N,Db]) =
      spter.split(db)

    // I have no more columns to take
    implicit def ZeroSplitter[Db <: DB] = new Splitter[_0, Db] {
      type Prefix = EOCol
      type Suffix = Db
      def split(db: Db) = (EOCol, db)
    }

    implicit def SuccSplitter[N <: Nat,
                              Db <: DB](implicit
                                        spter: Splitter[N,Db#Tail]) =
      new Splitter[Succ[N], Db] {
        type Prefix = |:[Db#Head, spter.Prefix]
        type Suffix = spter.Suffix
        def split(db: Db) = {
          val (pref, suff) = spter.split(db.tail)
          (|:(db.head, pref), suff)
        }
      }
  }

  /** Type class that withdraws the `n`th colum. */
  trait Withdrawer[N <: Nat, Db <: DB] {
    type Col
    type WithdrawDb <: DB
    type Out = (Col, WithdrawDb)
    def withdraw(db: Db): Out
  }

  object Withdrawer {
    def apply[N <: Nat, Db <: DB](db: Db)(implicit
                                          wdwer: Withdrawer[N,Db]) =
      wdwer.withdraw(db)

    implicit def OneWithdrawer[Db <: DB] = new Withdrawer[_1,Db] {
      type Col = Seq[Db#Head]
      type WithdrawDb = Db#Tail
      def withdraw(db: Db) = (db.head, db.tail)
    }

    implicit def SuccWithdrawer[N <: Nat,
                                Db <: DB](implicit
                                          wdwer: Withdrawer[N,Db#Tail]) =
      new Withdrawer[Succ[N],Db] {
        type Col = wdwer.Col
        type WithdrawDb = |:[Db#Head, wdwer.WithdrawDb]
        def withdraw(db: Db) = {
          val (col, withdrawDb) = wdwer.withdraw(db.tail)
          (col, |:(db.head, withdrawDb))
        }
      }
  }

  /** Type class that injects `col` at the `n`th position. */
  trait Injector[N <: Nat, Db <: DB, Col] {
    type Out <: DB
    def inject(db: Db, col: Seq[Col]): Out
  }

  object Injector {
    def apply[N <: Nat, Db <: DB, Col](db: Db,
                                       col: Seq[Col])(
                                       implicit
                                       ijtor: Injector[N,Db,Col]) =
      ijtor.inject(db, col)

    implicit def ZeroInject[Db <: DB, Col] = new Injector[_0,Db,Col] {
      type Out = |:[Col,Db]
      def inject(db: Db, col: Seq[Col]) = |:(col, db)
    }

    implicit def SuccInject[N <: Nat,
                            Db <: DB,
                            Col](implicit
                                 ijtor: Injector[N,Db#Tail,Col]) =
      new Injector[Succ[N],Db,Col] {
        type Out = |:[Db#Head, ijtor.Out]
        def inject(db: Db, col: Seq[Col]) =
          |:(db.head, ijtor.inject(db.tail, col))
      }
  }

  /** Type class that maps over a column at the `n`th position. */
  trait ColMapper[N <: Nat, Db <: DB, T, R] {
    type Out <: DB
    def map(db: Db)(f: T => R): Out
  }

  object ColMapper {
    def apply[N <: Nat,Db <: DB, T, R](db: Db)(
                                       f: T => R)(
                                       implicit
                                       cmper: ColMapper[N,Db,T,R]) =
      cmper.map(db)(f)

    implicit def UnColMapper[Db <: DB, T, R](implicit
                                             evApply: Db#Head <:< T) =
      new ColMapper[_1,Db,T,R] {
        type Out = |:[R, Db#Tail]
        def map(db: Db)(f: T => R) =
          |:(db.head.map{ h => f(h.asInstanceOf[T])}, db.tail)
      }

    implicit def SuccColMapper[N <: Nat,
                               Db <: DB,
                               T, R](implicit
                                     cmper: ColMapper[N,Db#Tail,T,R]) =
      new ColMapper[Succ[N],Db,T,R] {
        type Out = |:[Db#Head, cmper.Out]
        def map(db: Db)(f: T => R) = |:(db.head, cmper.map(db.tail)(f))
      }
  }

  object TakerV {
    def apply[Db <: DB](n: Int, db: Db): Db#This = DB._unsafe[Db#This](
      db match {
        case |:(h, t) => |:(h.take(n), TakerV(n, t))
        case _ => EOCol
      })
  }

  object DropperV {
    def apply[Db <: DB](n: Int, db: Db): Db#This = DB._unsafe[Db#This](
      db match {
        case |:(h, t) => |:(h.drop(n), DropperV(n, t))
        case _ => EOCol
      })
  }

  object SplitterV {
    def apply[Db <: DB](n: Int, db: Db) =
      (TakerV(n, db), DropperV(n, db))
  }
}
