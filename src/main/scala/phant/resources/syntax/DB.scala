package phant
package resources
package syntax

final class DBOps[Db <: DB](db: Db) {
  import ops.db._
  import shapeless._

  def take[N <: Nat](implicit taker: Taker[N, Db]) = Taker(db)

  def take(n: Nat)(implicit taker: Taker[n.N, Db]) = Taker(db)

  def drop[N <: Nat](implicit dpper: Dpper[N, Db]) = Dpper(db)

  def drop(n: Nat)(implicit dpper: Dpper[n.N, Db]) = Dpper(db)

  def split[N <: Nat](implicit taker: Taker[N,Db],
                               dpper: Dpper[N,Db]) = Splitter(db)

  def split(n: Nat)(implicit taker: Taker[n.N,Db],
                             dpper: Dpper[n.N,Db]) = Splitter(db)

  def takeV(n: Int) = TakerV(n, db)

  def dropV(n: Int) = DpperV(n, db)

  def splitV(n: Int) = SplitterV(n, db)
}
