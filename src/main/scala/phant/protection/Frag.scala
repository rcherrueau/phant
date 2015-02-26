package phant
package protection

import resources._
import ops.db._

import shapeless._

sealed trait Site
trait SiteA extends Site
trait SiteB extends Site

@annotation.implicitNotFound(msg = "${S1} and ${S2} are different site whereas they should be the same")
trait SameSite[S1 <: Site, S2 <: Site]
object SameSite {
  implicit def sameSite[S1 <: Site, S2 <: Site](implicit
                                                $ev: S1 =:= S2) =
    new SameSite[S1,S2] {}
}

final class Frag[Db <: DB, S <: Site](db: Db) {

}

object Frag {
  def split[Db <: DB, S1 <: Site, S2 <: Site](n: Nat, db: Db)(
    implicit sp: Splitter[n.N, Db]) = {
    val (sp1, sp2) = db.split(n)

    (new Frag[sp1.This,S1](sp1), new Frag[sp2.This,S2](sp2))
  }

  def join[Db1 <: DB, Db2 <: DB,
           S1 <: Site, S2 <: Site](f1: Frag[Db1, S1],
                                   f2: Frag[Db2, S2])(
                                   implicit
                                   $ev: SameSite[S1,S2]) = ???
}

object Test {
  import Nat._

  val db: String |: Option[String] |: Int |: EOCol = DB(
    ("2014-01-01", Some("Bob"),   1),
    ("2014-01-02", Some("Chuck"), 2),
    ("2014-01-03", Some("Bob"),   3),
    ("2014-01-04", Some("Chuck"), 4),
    ("2014-01-05", Some("Bob"),   5),
    ("2014-01-06", Some("Bob"),   5),
    ("2014-01-07", None,          5),
    ("2014-01-08", Some("Bob"),   6),
    ("2014-01-08", Some("Daan"),  6),
    ("2014-01-09", Some("Chuck"), 2),
    ("2014-01-10", Some("Chuck"), 7))

  val (f1, f2) = Frag.split[db.This, SiteA, SiteA](_2, db)
  Frag.join(f1, f2)

  val (f3, f4) = Frag.split[db.This, SiteA, SiteB](_2, db)
  // Frag.join(f3, f4) // Doesn't compile

}
