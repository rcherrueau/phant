package phant
package resources
package ops

import db._
import shapeless._

import org.scalatest._

class OpsDBSpec extends FlatSpec with Matchers {
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

  "Taker" should "take columns left to rigth at type level" in {
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

  "Dropper" should "drop columns left to rigth at type level" in {
    Dropper[_0, db.This](db)
    Dropper[_1, db.This](db)
    Dropper[_2, db.This](db)
    Dropper[_3, db.This](db)

    val $d0: String |: Option[String] |: Int |: EOCol =
      Dropper[_0, db.This](db)
    val $d1: Option[String] |: Int |: EOCol = Dropper[_1, db.This](db)
    val $d2: Int |: EOCol = Dropper[_2, db.This](db)
    val $d3: EOCol = Dropper[_3, db.This](db)
    // FIXME:
    // val $d4: EOCol = Dropper[_4, db.This](db)
  }

  "Splitter" should "split at type level at position `n`" in {
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

  "TakerV" should "produce chunck of DB type" in {
    TakerV(0,              db)
    TakerV(1,              db)
    TakerV(db.head.length, db)

    val $t0: String |: Option[String] |: Int |: EOCol = TakerV(0, db)
    val $t1: String |: Option[String] |: Int |: EOCol = TakerV(1, db)
    val $tN: String |: Option[String] |: Int |: EOCol =
      TakerV(db.head.length, db)
  }

  "DropperV" should "produce chunck of DB type" in {
    DropperV(0,              db)
    DropperV(1,              db)
    DropperV(db.head.length, db)

    val $d0: String |: Option[String] |: Int |: EOCol = DropperV(0, db)
    val $d1: String |: Option[String] |: Int |: EOCol = DropperV(1, db)
    val $dN: String |: Option[String] |: Int |: EOCol =
      DropperV(db.head.length, db)
  }

  "SplitterV" should "produce two chuncks typed as DB type" in {
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
