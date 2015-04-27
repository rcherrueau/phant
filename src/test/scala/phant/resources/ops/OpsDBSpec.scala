package phant
package resources
package ops

import utils._
import db._

import org.scalatest._

class OpsDBSpec extends FlatSpec with Matchers {
  import shapeless._, Nat._, ops.hlist._,
         syntax.std.tuple._

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
    Taker[_0, db.This](db): EOCol
    Taker[_1, db.This](db): String |: EOCol
    Taker[_2, db.This](db): String |: Option[String] |: EOCol
    Taker[_3, db.This](db): String |: Option[String] |: Int |: EOCol

    // FIXME:
    // illTyped("""
    //   // No implicit for _4
    //   Taker[_4, db.This](db)
    //   """)
  }

  "Dropper" should "drop columns left to rigth at type level" in {
    Dropper[_0, db.This](db): String |: Option[String] |: Int |: EOCol
    Dropper[_1, db.This](db): Option[String] |: Int |: EOCol
    Dropper[_2, db.This](db): Int |: EOCol
    Dropper[_3, db.This](db): EOCol

    // FIXME:
    // illTyped("""
    //   // No implicit for _4
    //   Dropper[_4, db.This](db)
    //   """)
  }

  "Splitter" should "split at type level at position `n`" in {
    Splitter[_0, db.This](db): (EOCol,
                                String |: Option[String] |: Int |: EOCol)
    Splitter[_1, db.This](db): (String |: EOCol,
                                Option[String] |: Int |: EOCol)
    Splitter[_2, db.This](db): (String |: Option[String] |: EOCol,
                                Int |: EOCol)
    Splitter[_3, db.This](db): (String |: Option[String] |: Int |: EOCol,
                                EOCol)

    // FIXME:
    // illTyped("""
    //   // No implicit for _4
    //   Splitter[_4, db.This](db)
    //   """)
  }

  "ColMapper" should "map over the `n`th columnq" in {
    ColMapper[_1, db.This, String, Option[String]](db)(Some(_)):
        Option[String] |: Option[String] |: Int |: EOCol
    ColMapper[_2, db.This, Option[String], String](db)(_.getOrElse("")):
        String |: String |: Int |: EOCol
    ColMapper[_3, db.This, Int, Unit](db)({ _ => ()}):
        String |: Option[String] |: Unit |: EOCol

    illTyped("""
      // No implicit for _0
      ColMapper[_0, db.This, Unit, Unit](db)(_ => ())
      """)
    illTyped("""
      // Expected type for column _1 is String
      ColMapper[_1, db.This, Int, Option[Int]](db)(Some(_))""")
  }

  "HeadLiner" should "return the first line with the rest of the DB" in {
    HeadLiner(db): Option[(String :: Option[String] :: Int :: HNil,
                           String |: Option[String] |: Int |: EOCol)]
    HeadLiner(DB()): Option[(HNil, EOCol)]

    HeadLiner(db) should be (
      Some(("2014-01-01" :: Some("Bob") :: 1 :: HNil,
            DB(("2014-01-02", Some("Chuck"), 2),
               ("2014-01-03", Some("Bob"),   3),
               ("2014-01-04", Some("Chuck"), 4),
               ("2014-01-05", Some("Bob"),   5),
               ("2014-01-06", Some("Bob"),   5),
               ("2014-01-07", None,          5),
               ("2014-01-08", Some("Bob"),   6),
               ("2014-01-08", Some("Daan"),  6),
               ("2014-01-09", Some("Chuck"), 2),
               ("2014-01-10", Some("Chuck"), 7)))))
    HeadLiner(DB()) should be (None)

    HeadLiner(DB(("2014-01-01", Some("Bob"),1))) should be (
      Some(("2014-01-01" :: Some("Bob") ::   1 :: HNil,
            |:(Nil: List[String],
               |:(Nil: List[Option[String]],
                  |:(Nil: List[Int], EOCol))))))

    def recurs[Db <: DB : HeadLiner](db: Db): Unit = HeadLiner(db) match {
      case line -: db => println(line) ; recurs(db)
      case None => println("fin")
    }

    recurs(db)

    Projection(db)({ case x :: y :: z :: HNil => x :: HNil }):
        String |: EOCol

    Projection(db)({ case x :: y :: z :: HNil => x :: z :: HNil }):
        String |: Int |: EOCol

    Projection(db)({
                     case x :: y :: z :: HNil => x :: z :: HNil
                   }) should be (DB(("2014-01-01", 1),
                                    ("2014-01-02", 2),
                                    ("2014-01-03", 3),
                                    ("2014-01-04", 4),
                                    ("2014-01-05", 5),
                                    ("2014-01-06", 5),
                                    ("2014-01-07", 5),
                                    ("2014-01-08", 6),
                                    ("2014-01-08", 6),
                                    ("2014-01-09", 2),
                                    ("2014-01-10", 7)))


    // FIXME:
    // Projection(db)({ case x :: y :: z :: HNil => HNil })
  }

  "TakerH" should "produce chunck of DB type" in {
    TakerH(0,              db): String |: Option[String] |: Int |: EOCol
    TakerH(1,              db): String |: Option[String] |: Int |: EOCol
    TakerH(db.head.length, db): String |: Option[String] |: Int |: EOCol
  }

  "DropperH" should "produce chunck of DB type" in {
    DropperH(0,              db): String |: Option[String] |: Int |: EOCol
    DropperH(1,              db): String |: Option[String] |: Int |: EOCol
    DropperH(db.head.length, db): String |: Option[String] |: Int |: EOCol
  }

  "SplitterH" should "produce two chuncks typed as DB type" in {
    SplitterH(0,              db): (String |: Option[String] |: Int |: EOCol,
                                    String |: Option[String] |: Int |: EOCol)
    SplitterH(1,              db): (String |: Option[String] |: Int |: EOCol,
                                    String |: Option[String] |: Int |: EOCol)
    SplitterH(db.head.length, db): (String |: Option[String] |: Int |: EOCol,
                                    String |: Option[String] |: Int |: EOCol)
  }
}
