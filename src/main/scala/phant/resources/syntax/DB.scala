package phant
package resources
package syntax

final class DBOps[Db <: DB](db: Db) {
  import ops.db._
  import shapeless.Nat

  def take[N <: Nat](implicit taker: Taker[N, Db]) = Taker(db)

  def take(n: Nat)(implicit taker: Taker[n.N, Db]) = Taker(db)

  def drop[N <: Nat](implicit dpper: Dropper[N, Db]) = Dropper(db)

  def drop(n: Nat)(implicit dpper: Dropper[n.N, Db]) = Dropper(db)

  def split[N <: Nat](implicit spter: Splitter[N,Db]) = Splitter(db)

  def split(n: Nat)(implicit spter: Splitter[n.N,Db]) = Splitter(db)

  def withdraw[N <: Nat](implicit wdwer: Withdrawer[N, Db]) = Withdrawer(db)

  def withdraw(n: Nat)(implicit wdwer: Withdrawer[n.N, Db]) = Withdrawer(db)

  def inject[N <: Nat,Col](col: Seq[Col])(implicit ijtor: Injector[N,Db,Col]) =
    Injector(db, col)

  def inject[Col](col: Seq[Col], n: Nat)(implicit ijtor: Injector[n.N,Db,Col]) =
    Injector(db, col)

  def mapCol[N <: Nat,T,R](f: T => R)(implicit cmper: ColMapper[N,Db,T,R]) =
    ColMapper(db)(f)

  def mapCol[T,R](f: T => R, n: Nat)(implicit cmper: ColMapper[n.N,Db,T,R]) =
    ColMapper(db)(f)

  def takeV(n: Int) = TakerV(n, db)

  def dropV(n: Int) = DropperV(n, db)

  def splitV(n: Int) = SplitterV(n, db)
}
