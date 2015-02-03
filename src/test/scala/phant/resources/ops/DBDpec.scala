package phant
package resources
package ops

import shapeless._
import db._

import org.scalatest._

class DBDpec extends FlatSpec with Matchers {
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

  "A DB" should "take columns left to rigth" in {
    Taker[_0, db.This](db)
    Taker[_1, db.This](db)
    Taker[_2, db.This](db)
    Taker[_3, db.This](db)

    val $t0: EOCol = Taker[_0, db.This](db)
    val $t1: String |: EOCol = Taker[_1, db.This](db)
    val $t2: String |: Option[String] |: EOCol = Taker[_2, db.This](db)
    val $t3: String |: Option[String] |: Int |: EOCol = Taker[_3, db.This](db)
    // FIXME:
    // val $t4: String |: Option[String] |: Int |: Nothing |: EOCol =
    //   Taker[_4, db.This](db)
  }

  "A DB" should "drop columns left to rigth" in {
    Dpper[_0, db.This](db)
    Dpper[_1, db.This](db)
    Dpper[_2, db.This](db)
    Dpper[_3, db.This](db)

    val $d0: String |: Option[String] |: Int |: EOCol = Dpper[_0, db.This](db)
    val $d1: Option[String] |: Int |: EOCol = Dpper[_1, db.This](db)
    val $d2: Int |: EOCol = Dpper[_2, db.This](db)
    val $d3: EOCol = Dpper[_3, db.This](db)
    // FIXME:
    // val $d4: EOCol = Dpper[_4, db.This](db)
  }

  "A DB" should "be split correctly" in {
    Splitter[_0, db.This](db)
    Splitter[_1, db.This](db)
    Splitter[_2, db.This](db)
    Splitter[_3, db.This](db)

    val $s0: (EOCol, String |: Option[String] |: Int |: EOCol) =
      Splitter[_0, db.This](db)
    val $s1: (String |: EOCol, Option[String] |: Int |: EOCol) =
      Splitter[_1, db.This](db)
    val $s2: (String |: Option[String] |: EOCol, Int |: EOCol) =
      Splitter[_2, db.This](db)
    val $s3: (String |: Option[String] |: Int |: EOCol, EOCol) =
      Splitter[_3, db.This](db)
    // FIXME:
    // val $s4: (String |: Option[String] |: Int |: Nothing |:EOCol, EOCol) =
    //   Splitter[_4, db.This](db)
  }

  "A DB" should "be take vertically from top to bottom" in {
    TakerV(0,              db)
    TakerV(1,              db)
    TakerV(db.head.length, db)

    val $t0: String |: Option[String] |: Int |: EOCol = TakerV(0, db)
    val $t1: String |: Option[String] |: Int |: EOCol = TakerV(1, db)
    val $tN: String |: Option[String] |: Int |: EOCol =
      TakerV(db.head.length, db)
  }

  "A DB" should "be drop vertically from top to bottom" in {
    DpperV(0,              db)
    DpperV(1,              db)
    DpperV(db.head.length, db)

    val $d0: String |: Option[String] |: Int |: EOCol = DpperV(0, db)
    val $d1: String |: Option[String] |: Int |: EOCol = DpperV(1, db)
    val $dN: String |: Option[String] |: Int |: EOCol =
      DpperV(db.head.length, db)
  }

  "A DB" should "be split vertically correctly" in {
    SplitterV(0,              db)
    SplitterV(1,              db)
    SplitterV(db.head.length, db)

    val $s0: (String |: Option[String] |: Int |: EOCol,
              String |: Option[String] |: Int |: EOCol) = SplitterV(0, db)
    val $s1: (String |: Option[String] |: Int |: EOCol,
              String |: Option[String] |: Int |: EOCol) = SplitterV(1, db)
    val $sN: (String |: Option[String] |: Int |: EOCol,
              String |: Option[String] |: Int |: EOCol) =
      SplitterV(db.head.length, db)
  }
}
