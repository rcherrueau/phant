package phant
package resources

import db._
import nat._

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
    val col0: EOCol = db.take(_0)
    val col1: String |: EOCol = db.take(_1)
    val col2: String |: Option[String] |: EOCol = db.take(_2)
    val col3: String |: Option[String] |: Int |: EOCol = db.take(_3)

    col0.length.value should be (_0.value)
    col1.length.value should be (_1.value)
    col2.length.value should be (_2.value)
    col3.length.value should be (_3.value)
  }

  "A DB" should "drop columns left to rigth" in {
    // BUG: Type inference is not available here due to scala 2.11
    // bug. See, https://issues.scala-lang.org/browse/SI-8252
    val col3: String |: Option[String] |: Int |: EOCol = db.drop(_0)
    val col2: Option[String] |: Int |: EOCol = db.drop(_1)
    val col1: Int |: EOCol = db.drop(_2)
    val col0: EOCol = db.drop(_3)

    col3.length.value should be (_3.value)
    col2.length.value should be (_2.value)
    col1.length.value should be (_1.value)
    col0.length.value should be (_0.value)
  }

  "A DB" should "be split correctly" in {
    val sp1: (EOCol, String |: Option[String] |: Int |: EOCol) = db.split(_0)
    val sp2 = db.split(_1)
    val sp3: (String |: Option[String] |: EOCol, Int |: EOCol) = db.split(_2)
    val sp4: (String |: Option[String] |: Int |: EOCol, EOCol) = db.split(_3)
  }

  "A DB" should "be take vertically from top to bottom" in {
    val st0: String |: Option[String] |: Int |: EOCol = db.takeV(0)
    val st1: String |: Option[String] |: Int |: EOCol = db.takeV(1)
    val st2: String |: Option[String] |: Int |: EOCol = db.takeV(2)
    val st3: String |: Option[String] |: Int |: EOCol = db.takeV(3)

    st0.lengthV should be (0)
    st1.lengthV should be (1)
    st2.lengthV should be (2)
    st3.lengthV should be (3)
  }

  "A DB" should "be drop vertically from top to bottom" in {
    val st0: String |: Option[String] |: Int |: EOCol = db.dropV(0)
    val st1: String |: Option[String] |: Int |: EOCol = db.dropV(1)
    val st2: String |: Option[String] |: Int |: EOCol = db.dropV(2)
    val st3: String |: Option[String] |: Int |: EOCol = db.dropV(3)

    st0.lengthV should be (db.lengthV - 0)
    st1.lengthV should be (db.lengthV - 1)
    st2.lengthV should be (db.lengthV - 2)
    st3.lengthV should be (db.lengthV - 3)
  }

  "A DB" should "be split vertically correctly" in {
    val sp0: (String |: Option[String] |: Int |: EOCol,
              String |: Option[String] |: Int |: EOCol) = db.splitV(0)
    val sp1: (String |: Option[String] |: Int |: EOCol,
              String |: Option[String] |: Int |: EOCol) = db.splitV(1)
    val sp2: (String |: Option[String] |: Int |: EOCol,
              String |: Option[String] |: Int |: EOCol) = db.splitV(2)
    val sp3: (String |: Option[String] |: Int |: EOCol,
              String |: Option[String] |: Int |: EOCol) = db.splitV(3)
  }
}
