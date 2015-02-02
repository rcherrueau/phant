package phant
package resources
package ops

import resources.db._
import db._

import org.scalatest._

class DBDpec extends FlatSpec with Matchers {
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

  "A DB" should "take columns left to rigth" in {
    Taker(Zero(), db)
    Taker(Succ(Zero()), db)
    Taker(Succ(Succ(Zero())), db)
    Taker(Succ(Succ(Succ(Zero()))), db)

    val $t0: EOCol = Taker(Zero(), db)
    val $t1: String |: EOCol = Taker(Succ(Zero()), db)
    val $t2: String |: Option[String] |: EOCol = Taker(Succ(Succ(Zero())), db)
    val $t3: String |: Option[String] |: Int |: EOCol =
      Taker(Succ(Succ(Succ(Zero()))), db)
    // FIXME:
    // val $t4: String |: Option[String] |: Int |: Nothing |: EOCol =
    //   Taker(Succ(Succ(Succ(Succ(Zero())))), db)
  }

  "A DB" should "drop columns left to rigth" in {
    Dpper(Zero(), db)
    Dpper(Succ(Zero()), db)
    Dpper(Succ(Succ(Zero())), db)
    Dpper(Succ(Succ(Succ(Zero()))), db)

    val $d0: String |: Option[String] |: Int |: EOCol = Dpper(Zero(), db)
    val $d1: Option[String] |: Int |: EOCol = Dpper(Succ(Zero()), db)
    val $d2: Int |: EOCol = Dpper(Succ(Succ(Zero())), db)
    val $d3: EOCol = Dpper(Succ(Succ(Succ(Zero()))), db)
    // FIXME:
    // val $d4: EOCol = Dpper(Succ(Succ(Succ(Succ(Zero())))), db)
  }

  "A DB" should "be split correctly" in {
    Splitter(Zero(), db)
    Splitter(Succ(Zero()), db)
    Splitter(Succ(Succ(Zero())), db)
    Splitter(Succ(Succ(Succ(Zero()))), db)

    val $s0: (EOCol, String |: Option[String] |: Int |: EOCol) =
      Splitter(Zero(), db)
    val $s1: (String |: EOCol, Option[String] |: Int |: EOCol) =
      Splitter(Succ(Zero()), db)
    val $s2: (String |: Option[String] |: EOCol, Int |: EOCol) =
      Splitter(Succ(Succ(Zero())), db)
    val $s3: (String |: Option[String] |: Int |: EOCol, EOCol) =
      Splitter(Succ(Succ(Succ(Zero()))), db)
    // FIXME:
    // val $s4: (String |: Option[String] |: Int |: Nothing |:EOCol, EOCol) =
    //   Splitter(Succ(Succ(Succ(Succ(Zero())))), db)
  }

  "A DB" should "be take vertically from top to bottom" in {
  }

  "A DB" should "be drop vertically from top to bottom" in {
  }

  "A DB" should "be split vertically correctly" in {
  }
}
