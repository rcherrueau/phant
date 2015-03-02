package phant
package resources

import ops.db._

import shapeless.Nat._
import org.scalatest._

class DBSpec extends FlatSpec with Matchers {
  val db: String |: Option[String] |: Int |: EOCol =
    DB(("2014-01-01", Some("Bob"),   1),
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
    db.take(_0) should be (DB())

    db.take(_1) should be (DB(("2014-01-01"),
                              ("2014-01-02"),
                              ("2014-01-03"),
                              ("2014-01-04"),
                              ("2014-01-05"),
                              ("2014-01-06"),
                              ("2014-01-07"),
                              ("2014-01-08"),
                              ("2014-01-08"),
                              ("2014-01-09"),
                              ("2014-01-10")))

    db.take(_2) should be (DB(("2014-01-01", Some("Bob")),
                              ("2014-01-02", Some("Chuck")),
                              ("2014-01-03", Some("Bob")),
                              ("2014-01-04", Some("Chuck")),
                              ("2014-01-05", Some("Bob")),
                              ("2014-01-06", Some("Bob")),
                              ("2014-01-07", None),
                              ("2014-01-08", Some("Bob")),
                              ("2014-01-08", Some("Daan")),
                              ("2014-01-09", Some("Chuck")),
                              ("2014-01-10", Some("Chuck"))))

    db.take(_3) should be (DB(("2014-01-01", Some("Bob"),   1),
                              ("2014-01-02", Some("Chuck"), 2),
                              ("2014-01-03", Some("Bob"),   3),
                              ("2014-01-04", Some("Chuck"), 4),
                              ("2014-01-05", Some("Bob"),   5),
                              ("2014-01-06", Some("Bob"),   5),
                              ("2014-01-07", None,          5),
                              ("2014-01-08", Some("Bob"),   6),
                              ("2014-01-08", Some("Daan"),  6),
                              ("2014-01-09", Some("Chuck"), 2),
                              ("2014-01-10", Some("Chuck"), 7)))
  }

  "A DB" should "drop columns left to rigth" in {
    db.drop(_0) should be (DB(("2014-01-01", Some("Bob"),   1),
                             ("2014-01-02", Some("Chuck"), 2),
                             ("2014-01-03", Some("Bob"),   3),
                             ("2014-01-04", Some("Chuck"), 4),
                             ("2014-01-05", Some("Bob"),   5),
                             ("2014-01-06", Some("Bob"),   5),
                             ("2014-01-07", None,          5),
                             ("2014-01-08", Some("Bob"),   6),
                             ("2014-01-08", Some("Daan"),  6),
                             ("2014-01-09", Some("Chuck"), 2),
                             ("2014-01-10", Some("Chuck"), 7)))

    db.drop(_1) should be (DB((Some("Bob"),   1),
                              (Some("Chuck"), 2),
                              (Some("Bob"),   3),
                              (Some("Chuck"), 4),
                              (Some("Bob"),   5),
                              (Some("Bob"),   5),
                              (None,          5),
                              (Some("Bob"),   6),
                              (Some("Daan"),  6),
                              (Some("Chuck"), 2),
                              (Some("Chuck"), 7)))

    db.drop(_2) should be (DB((1),
                              (2),
                              (3),
                              (4),
                              (5),
                              (5),
                              (5),
                              (6),
                              (6),
                              (2),
                              (7)))

    db.drop(_3) should be (DB())
  }

  "A DB" should "produce two chuncks of columns on split" in {
    db.split(_0) should be ((DB(),
                             DB(("2014-01-01", Some("Bob"),   1),
                                ("2014-01-02", Some("Chuck"), 2),
                                ("2014-01-03", Some("Bob"),   3),
                                ("2014-01-04", Some("Chuck"), 4),
                                ("2014-01-05", Some("Bob"),   5),
                                ("2014-01-06", Some("Bob"),   5),
                                ("2014-01-07", None,          5),
                                ("2014-01-08", Some("Bob"),   6),
                                ("2014-01-08", Some("Daan"),  6),
                                ("2014-01-09", Some("Chuck"), 2),
                                ("2014-01-10", Some("Chuck"), 7))))

    db.split(_1) should be ((DB(("2014-01-01"),
                                ("2014-01-02"),
                                ("2014-01-03"),
                                ("2014-01-04"),
                                ("2014-01-05"),
                                ("2014-01-06"),
                                ("2014-01-07"),
                                ("2014-01-08"),
                                ("2014-01-08"),
                                ("2014-01-09"),
                                ("2014-01-10")),
                             DB((Some("Bob"),   1),
                                (Some("Chuck"), 2),
                                (Some("Bob"),   3),
                                (Some("Chuck"), 4),
                                (Some("Bob"),   5),
                                (Some("Bob"),   5),
                                (None,          5),
                                (Some("Bob"),   6),
                                (Some("Daan"),  6),
                                (Some("Chuck"), 2),
                                (Some("Chuck"), 7))))


    db.split(_2) should be ((DB(("2014-01-01", Some("Bob")),
                              ("2014-01-02", Some("Chuck")),
                              ("2014-01-03", Some("Bob")),
                              ("2014-01-04", Some("Chuck")),
                              ("2014-01-05", Some("Bob")),
                              ("2014-01-06", Some("Bob")),
                              ("2014-01-07", None),
                              ("2014-01-08", Some("Bob")),
                              ("2014-01-08", Some("Daan")),
                              ("2014-01-09", Some("Chuck")),
                              ("2014-01-10", Some("Chuck"))),
                             DB((1),
                                (2),
                                (3),
                                (4),
                                (5),
                                (5),
                                (5),
                                (6),
                                (6),
                                (2),
                                (7))))

    db.split(_3) should be ((DB(("2014-01-01", Some("Bob"),   1),
                                ("2014-01-02", Some("Chuck"), 2),
                                ("2014-01-03", Some("Bob"),   3),
                                ("2014-01-04", Some("Chuck"), 4),
                                ("2014-01-05", Some("Bob"),   5),
                                ("2014-01-06", Some("Bob"),   5),
                                ("2014-01-07", None,          5),
                                ("2014-01-08", Some("Bob"),   6),
                                ("2014-01-08", Some("Daan"),  6),
                                ("2014-01-09", Some("Chuck"), 2),
                                ("2014-01-10", Some("Chuck"), 7)),
                             DB()))
  }

  "A DB" should "take lines from top to bottom" in {
    db.takeH(0) should be (DB[String, Option[String], Int](Nil:_*))

    db.takeH(1) should be (DB(("2014-01-01", Some("Bob"),1)))

    db.takeH(db.head.length) should be (db)
  }

  "A DB" should "drop lines from top to bottom" in {
    db.dropH(0) should be (db)

    db.dropH(1) should be (DB(("2014-01-02", Some("Chuck"), 2),
                              ("2014-01-03", Some("Bob"),   3),
                              ("2014-01-04", Some("Chuck"), 4),
                              ("2014-01-05", Some("Bob"),   5),
                              ("2014-01-06", Some("Bob"),   5),
                              ("2014-01-07", None,          5),
                              ("2014-01-08", Some("Bob"),   6),
                              ("2014-01-08", Some("Daan"),  6),
                              ("2014-01-09", Some("Chuck"), 2),
                              ("2014-01-10", Some("Chuck"), 7)))

    db.dropH(db.head.length) should be (DB[String, Option[String], Int](
                                          Nil:_*))
  }

  "A DB" should "produce two chuncks of DB on splitH" in {
    db.splitH(0) should be ((DB[String, Option[String], Int](Nil:_*), db))

    db.splitH(1) should be ((DB(("2014-01-01", Some("Bob"),1)),
                             DB(("2014-01-02", Some("Chuck"), 2),
                                ("2014-01-03", Some("Bob"),   3),
                                ("2014-01-04", Some("Chuck"), 4),
                                ("2014-01-05", Some("Bob"),   5),
                                ("2014-01-06", Some("Bob"),   5),
                                ("2014-01-07", None,          5),
                                ("2014-01-08", Some("Bob"),   6),
                                ("2014-01-08", Some("Daan"),  6),
                                ("2014-01-09", Some("Chuck"), 2),
                                ("2014-01-10", Some("Chuck"), 7))))

    db.splitH(db.head.length) should be ((db,
                                          DB[String, Option[String], Int](
                                            Nil:_*)))
  }
}
