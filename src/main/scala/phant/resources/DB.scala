package phant
package resources

import shapeless._, shapeless.ops.hlist._

sealed abstract class DB {
  type This >: this.type <: DB

  /** Type of the first column. */
  type Head
  def head: Seq[Head]

  /** Type of the rest of the DB. */
  type Tail <: DB
  def tail: Tail

  /** Type of a Line. */
  type Line <: HList

  /** Tests if the database is empty. */
  def isEmpty: Boolean = head.isEmpty

  /** Counts the number of lines in the DB. */
  def lines: Int = head.length

  /** Returns the first line of the Database. */
  def line(implicit tupler: Tupler[This#Line]): Option[tupler.Out] =
    this._line map { tupler(_) }

  // helper for line
  protected[phant] def _line: Option[Line]

  /** Returns the first line of Database with the rest of it. */
  def hview(implicit
            tupler: Tupler[This#Line]): Option[(tupler.Out, This)] =
    this._hview map { case (line, db) => (tupler(line), db) }

  // helper for hview
  protected[phant] def _hview: Option[(Line, This)]

  // def filter(implicit
  //            tupler: Tupler[This#Line]): (tupler.Out => Boolean) => This =
  //   (f: (tupler.Out => Boolean)) => {
  //     def _filter[Db <: DB](db: Db): Db = db.hview match {
  //       case line -: db => if (f(line)) line -:
  //     }
  //   }

  // ("2014-01-02" :: Some("Chuck") :: 2 :: HNil) -: db
  /** Inserts a new line in the DB. */
  def -:[L <: HList](line: L): This = line match {
    case hd :: tl => DB._unsafe[This](|:(hd +: head, tl -: tail))
    case HNil => this match {
      case |:(col, db) if !col.isEmpty => {
        val str = s"""
                  |db  = ${this}
                  """.stripMargin
        throw new NoSuchElementException("\n" + str)
      }
      case _ => DB._unsafe[This](EOCol)
    }
  }

  // // TODO: Let's try to put select into DBOps. Thus avoids the
  // // implcitly in `db.select(implicitly) { case (x,y,z) => true }
  // def select(implicit tupler: Tupler[This#Line]):
  //     (tupler.Out => Boolean) => This =
  //   (f: (tupler.Out => Boolean)) => {
  //     def _filter[Db <: DB](db: Db): Db = db._hview match {
  //       case line -: db =>
  //         if (f(tupler(DB._unsafe[This#Line](line))))
  //           DB._unsafe[Db](line -: _filter(db))
  //         else DB._unsafe[Db](_filter(db))
  //       case None => db
  //     }

  //     DB._unsafe[This](_filter(this))
  //   }

  def select: (Line => Boolean) => This =
    (f: (Line => Boolean)) => _select(f)

  protected[phant] def _select(f: Line => Boolean): This


  override def toString = {
    def mkLine(l: HList): String = l match {
      case hd :: HNil => hd.toString
      case hd :: tl => hd.toString + ",\t" + mkLine(tl)
      case HNil => ""
    }

    this._hview match {
      case line -: db => mkLine(line) + "\n" + db.toString
      case None => ""
    }
  }
}

final case class |:[H, T <: DB](val head: Seq[H],
                                val tail: T) extends DB {
  type Head = H
  type Tail = T
  type This = |:[Head,Tail]
  type Line = Head :: Tail#Line

  def _line: Option[Line] =
    if (!isEmpty) tail._line map (head.head :: _) else None

  def _hview: Option[(Line, This)] =
    if (!isEmpty) {
      tail._hview map {
        case (tVal, tCol) =>
          (head.head :: tVal, |:(head.tail, DB._unsafe[Tail](tCol)))
      }
    }
    else None

  def _select(f: Line => Boolean): This = this._hview match {
    case line -: db => if (f(line)) line -: db._select(f)
                       else db._select(f)
    case None => this
  }

  override def equals(o: Any): Boolean = o match {
    case |:(h, t) => head == h
    case _ => false
  }
}

trait EOCol extends DB {
  type Head = Nothing
  type Tail = Nothing
  type This = EOCol
  type Line = HNil

  def head = throw new NoSuchElementException("DB.head")
  def tail = throw new NoSuchElementException("DB.tail")

  def _line: Option[HNil] = Some(HNil)
  def _hview: Option[(HNil, EOCol)] = Some((HNil, EOCol))
  def _select(f: HNil => Boolean): EOCol = EOCol

  override def isEmpty = true
  override def lines = throw new NoSuchElementException("DB.lines")

  override def equals(o: Any): Boolean = o match {
    case Nil => true
    case _ => false
  }
}
final object EOCol extends EOCol

object DB {
  def apply(): EOCol = EOCol

  def apply[T1](ts: (T1)*): |:[T1,EOCol] = |:(ts.toList, EOCol)

  // Implicits are there to avoid apply ambiguity after type
  // erasure.
  def apply[T1,T2](ts: (T1, T2)*)(implicit
                                  $d01: DummyImplicit):
      |:[T1,|:[T2,EOCol]] = {
    val (t1s, t2s) = ts.foldLeft((Nil:List[T1],Nil:List[T2])) {
      case ((t1s, t2s), (t1, t2)) => (t1 :: t1s, t2 :: t2s)
    }

    |:(t1s.reverse, |:(t2s.reverse, EOCol))
  }

  def apply[T1,T2,T3](ts: (T1,T2,T3)*)(implicit
                                       $d01: DummyImplicit,
                                       $d02: DummyImplicit):
      |:[T1,|:[T2,|:[T3,EOCol]]] = {
    val (t1s, t2s, t3s) =
      ts.foldLeft((Nil:List[T1],Nil:List[T2],Nil:List[T3])) {
        case ((t1s, t2s, t3s), (t1, t2, t3)) =>
          (t1 :: t1s, t2 :: t2s, t3 :: t3s)
      }

    |:(t1s.reverse, |:(t2s.reverse, |:(t3s.reverse, EOCol)))
  }

  // Convert this DB into DBOps: "pimp-my-library" pattern
  import syntax.DBOps
  import scala.language.implicitConversions
  implicit def db2dbOps[Db <: DB](db: Db): DBOps[Db] =
    new DBOps(db)

  def _unsafe[T](f: => Any) = f.asInstanceOf[T]
}


/** Horizontal deconstructor
  *
  * Usage:
  * {{{
  * HeadLiner(db) match {
  *   case hd -: db => ()
  *   case None =>
  * }
  * }}}
  */
object -: {
  def unapply[L <: HList,
              Db <: DB](p: Option[(L, Db)]): Option[(L,Db)]
    = p flatMap { case (l,db) => Some(l,db) }
}
