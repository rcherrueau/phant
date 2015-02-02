package phant
package resources

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
  }

  "A DB" should "drop columns left to rigth" in {
  }

  "A DB" should "be split correctly" in {
  }

  "A DB" should "be take vertically from top to bottom" in {
  }

  "A DB" should "be drop vertically from top to bottom" in {
  }

  "A DB" should "be split vertically correctly" in {
  }
}
