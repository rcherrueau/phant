package phant

object Guard3 {
  import shapeless._, Nat._
  import scalaz._, StateT._
  import DB._

  type Idx = Int
  type Guard3[S1,S2,A] = IndexedState[S1,S2,A]

  /** Configures the shape of the DB. */
  def configure[C1,C2,C3]: Guard3[Site0[DB[(Raw[C1],Raw[C2],Raw[C3])]],
                                  Site0[DB[(Raw[C1],Raw[C2],Raw[C3])]],
                                  Unit] =
    State(s => (s, ()))

  /** Encrypts the first column of the DB. */
  def crypt[C1,C2,C3,
            S[X] <: Site[X,S],
            R1[C1] <: Rsc,
            R2[C2] <: Rsc,
            R3[C3] <: Rsc,
            PT[C1] <: Protected](
    n: _1)(
    f: R1[C1] => PT[C1]): Guard3[S[DB[(R1[C1], R2[C2], R3[C3])]],
                                 S[DB[(PT[C1], R2[C2], R3[C3])]],
                                 Unit] =
    State.iModify(s => s(s.get map { case (c1, c2, c3) => (f(c1), c2, c3) }))


  /** Encrypts the second column of the DB. */
  def crypt[C1,C2,C3,
            S[X] <: Site[X,S],
            R1[C1] <: Rsc,
            R2[C2] <: Rsc,
            R3[C3] <: Rsc,
            PT[C2] <: Protected](
    n: _2)(
    f: R2[C2] => PT[C2])(implicit $dm: DummyImplicit):
      Guard3[S[DB[(R1[C1], R2[C2], R3[C3])]],
             S[DB[(R1[C1], PT[C2], R3[C3])]],
             Unit] =
    State.iModify(s => s(s.get map { case (c1, c2, c3) => (c1, f(c2), c3) }))

  /** Encrypts the third column of the DB. */
  def crypt[C1,C2,C3,
            S[X] <: Site[X,S],
            R1[C1] <: Rsc,
            R2[C2] <: Rsc,
            R3[C3] <: Rsc,
            PT[C3] <: Protected](
    n: _3)(
    f: R3[C3] => PT[C3])(implicit
                         $dm1: DummyImplicit,
                         $dm2: DummyImplicit):
      Guard3[S[DB[(R1[C1], R2[C2], R3[C3])]],
             S[DB[(R1[C1], R2[C2], PT[C3])]],
             Unit] =
    State.iModify(s => s(s.get map { case (c1, c2, c3) => (c1, c2, f(c3)) }))

  /** Decrypts the first column of the DB. */
  def decrypt[C1,C2,C3,
              S[X] <: Site[X,S],
              R1[C1] <: Rsc,
              R2[C2] <: Rsc,
              R3[C3] <: Rsc,
              PT[C1] <: Protected](
    n: _1)(
    f: PT[C1] => R1[C1]): Guard3[S[DB[(PT[C1], R2[C2], R3[C3])]],
                                 S[DB[(R1[C1], R2[C2], R3[C3])]],
                                 Unit] =
    State.iModify(s => s(s.get map { case (c1, c2, c3) => (f(c1), c2, c3) }))

  /** Decrypts the second column of the DB. */
  def decrypt[C1,C2,C3,
            S[X] <: Site[X,S],
            R1[C1] <: Rsc,
            R2[C2] <: Rsc,
            R3[C3] <: Rsc,
            PT[C2] <: Protected](
    n: _2)(
    f: PT[C2] => R2[C2])(implicit $dm: DummyImplicit):
      Guard3[S[DB[(R1[C1], PT[C2], R3[C3])]],
             S[DB[(R1[C1], R2[C2], R3[C3])]],
             Unit] =
    State.iModify(s => s(s.get map { case (c1, c2, c3) => (c1, f(c2), c3) }))

  /** Decrypts the third column of the DB. */
  def decrypt[C1,C2,C3,
              S[X] <: Site[X,S],
              R1[C1] <: Rsc,
              R2[C2] <: Rsc,
              R3[C3] <: Rsc,
              PT[C3] <: Protected](
    n: _3)(
    f: PT[C3] => R3[C3])(implicit
                         $dm1: DummyImplicit,
                         $dm2: DummyImplicit):
      Guard3[S[DB[(R1[C1], R2[C2], PT[C3])]],
             S[DB[(R1[C1], R2[C2], R3[C3])]],
             Unit] =
    State.iModify(s => s(s.get map { case (c1, c2, c3) => (c1, c2, f(c3)) }))

  /** Vertically fragments on the first column of the DB. */
  def fragV[C1,C2,C3,
            S1[X] <: Site[X,S1],
            S2[X] <: Site[X,S2]](
    n: _1)(
    s1: S1[_],
    s2: S2[_]): Guard3[Site0[DB[(C1, C2, C3)]],
                       (S1[DB[(C1, Idx)]], S2[DB[(C2, C3, Idx)]]),
                       Unit] =
    State.iModify(s => {
                    val (lf, rf) = s.get.unzip(r => ((r._1), (r._2, r._3)))
                    (s1(lf.zipWithIndex), s2(rf.foldLeft((Nil:DB[(C2,C3,Idx)], 0)) {
                                               case ((db, i), (c2, c3)) =>
                                                 ((c2, c3, i) :: db, i + 1)
                                             }._1))
                  })

  /** Vertically fragments on the second column of the DB. */
  def fragV[C1,C2,C3,
            S1[X] <: Site[X,S1],
            S2[X] <: Site[X,S2]](
    n: _2)(
    s1: S1[_],
    s2: S2[_])(implicit $dm: DummyImplicit):
      Guard3[Site0[DB[(C1, C2, C3)]],
             (S1[DB[(C1, C2, Idx)]], S2[DB[(C3, Idx)]]),
             Unit] =
    State.iModify(s => {
                    val (lf, rf) = s.get.unzip(r => ((r._1, r._2), (r._3)))
                    (s1(lf.foldLeft((Nil:DB[(C1,C2,Idx)], 0)) {
                          case ((db, i), (c1, c2)) =>
                            ((c1, c2, i) :: db, i + 1)
                        }._1), s2(rf.zipWithIndex))
                  })

  /** Defragments a vertically fragmented DB on the first column. */
  def defragV[C1,C2,C3,
              S1[X] <: Site[X,S1],
              S2[X] <: Site[X,S2]](
    n: _1): Guard3[(S1[DB[(C1, Idx)]], S2[DB[(C2, C3, Idx)]]),
                   Site0[DB[(C1,C2,C3)]],
                   Unit] =
    State.iModify(s => {
                    val (lf, rf) = s
                    Site0(for {
                            (c1, i) <- lf.get
                            (c2, c3, j) <- rf.get
                            if (i == j)
                          } yield (c1, c2, c3))
                  })

  /** Defragments a vertically fragmented DB on the second column. */
  def defragV[C1,C2,C3,
              S1[X] <: Site[X,S1],
              S2[X] <: Site[X,S2]](
    n: _2)(implicit $dm: DummyImplicit): 
      Guard3[(S1[DB[(C1, C2, Idx)]], S2[DB[(C3, Idx)]]),
             Site0[DB[(C1,C2,C3)]],
             Unit] =
    State.iModify(s => {
                    val (lf, rf) = s
                    Site0(for {
                            (c1, c2, i) <- lf.get
                            (c3, j) <- rf.get
                            if (i == j)
                          } yield (c1, c2, c3))
                  })

  /** Executes a query on the DB. */
  def query[X,Q,
            S[X] <: Site[X,S]](q: X => Q): Guard3[S[X], S[X], S[Q]] =
    State.gets(s => s(q(s.get)))

  /** Executes a query on the left fragment of a DB. */
  def queryL[X,Q,SR,
             SL[X] <: Site[X,SL]](q: X => Q): Guard3[(SL[X], SR),
                                                     (SL[X], SR),
                                                     SL[Q]] =
    State.gets({ case (sl, _) => sl(q(sl.get)) })

  /** Executes a query on the right fragment of a DB. */
  def queryR[X,Q,SL,
             SR[X] <: Site[X,SR]](q: X => Q): Guard3[(SL, SR[X]),
                                                     (SL, SR[X]),
                                                     SR[Q]] =
    State.gets({ case (_, sr) => sr(q(sr.get)) })
}

object DB {
  import spire.algebra._, spire.implicits._

  type DB[X] = List[X]

  implicit def Π3toC1[C1,C2,C3,
                      R1[C1] <: Rsc,
                      R2[C2] <: Rsc,
                      R3[C3] <: Rsc](r: (R1[C1], R2[C2], R3[C3])): R1[C1] = r._1
  implicit def Π3toC2[C1,C2,C3,
                      R1[C1] <: Rsc,
                      R2[C2] <: Rsc,
                      R3[C3] <: Rsc](r: (R1[C1], R2[C2], R3[C3])): R2[C2] = r._2
  implicit def Π3toC3[C1,C2,C3,
                      R1[C1] <: Rsc,
                      R2[C2] <: Rsc,
                      R3[C3] <: Rsc](r: (R1[C1], R2[C2], R3[C3])): R3[C3] = r._3
  implicit def Π2toC1[C1,C2,
                      R1[C1] <: Rsc,
                      R2[C2] <: Rsc](r: (R1[C1], R2[C2])): R1[C1] = r._1
  implicit def Π2toC2[C1,C2,
                      R1[C1] <: Rsc,
                      R2[C2] <: Rsc](r: (R1[C1], R2[C2])): R2[C2] = r._2
  def Π[T, C](db: DB[T])(p: T => C): DB[C] = db.map(p)
  def σ[T, TT](db: DB[T])(p: TT => Boolean)(implicit Π: T => TT): DB[T] =
    db.foldLeft(Nil:DB[T])((db, r) => if (p(Π(r))) r :: db
                                            else db)
  def group[T, U : Eq](db: DB[T])(p: T => U): List[DB[T]] = db match {
    case Nil => Nil
    case line :: db =>
      (line :: db.filter(p(_) === p(line))) ::
        group (db.filter(p(_) =!= p(line))) (p)
  }
}

object Guard3Test extends App {
  import shapeless._, Nat._
  import spire.algebra._, spire.implicits._
  import Guard3._
  import DB._

  case class Date(get: String)
  object Date {
    implicit def order: Order[Date] = new Order[Date] {
      override def compare(x: Date, y: Date) =
        implicitly[Order[String]].compare(x.get, y.get)
    }
  }

  case class Name(get: String)
  object Name {
    implicit def order: Order[Name] = new Order[Name] {
      override def compare(x: Name, y: Name) =
        implicitly[Order[String]].compare(x.get, y.get)
    }
  }

  case class Addr(get: Option[Int])
  object Addr {
    implicit def order: Order[Addr] = new Order[Addr] {
      override def compare(x: Addr, y: Addr) =
        implicitly[Order[Option[Int]]].compare(x.get, y.get)
    }
  }

  def date[R1[Date] <: Rsc,
           R2[Name] <: Rsc,
           R3[Addr] <: Rsc](r: (R1[Date], R2[Name], R3[Addr])): R1[Date] = r._1
  def date[R1[Date] <: Rsc](r: R1[Date]): R1[Date] = r

  def name[R1[Date] <: Rsc,
           R2[Name] <: Rsc,
           R3[Addr] <: Rsc](r: (R1[Date], R2[Name], R3[Addr])): R2[Name] = r._2

  def addr[R1[Date] <: Rsc,
           R2[Name] <: Rsc,
           R3[Addr] <: Rsc](r: (R1[Date], R2[Name], R3[Addr])): R3[Addr] = r._3

  def lastweek[R[Date] <: Rsc](d: R[Date]): Boolean = true
  def atdesk[R[Addr] <: Rsc](a: R[Addr]): Boolean = true

  val localApp: Guard3[Site0[DB[(Raw[Date], Raw[Name], Raw[Addr])]],
                       Site0[DB[(Raw[Date], Raw[Name], Raw[Addr])]],
                       _] =
     for {
       _ <- configure[Date, Name, Addr]
       q <- query((db: DB[(Raw[Date], Raw[Name], Raw[Addr])]) => {
                    val r1 = σ (db) (lastweek)
                    val r2 = σ (r1) (atdesk)
                    r2
                    // val r3 = Π (r2) (date)
                    // r3
                    // val r4 = group (r3) (date); r4
                    // val r5 = count (r4); r5
                  })
     } yield q

  val db: DB[(Raw[Date],Raw[Name],Raw[Addr])] =
    List((Date("2014-01-01"), Name("Bob"),   Addr(Some(1))),
         (Date("2014-01-02"), Name("Chuck"), Addr(Some(2))),
         (Date("2014-01-03"), Name("Bob"),   Addr(Some(3))),
         (Date("2014-01-04"), Name("Chuck"), Addr(Some(4))),
         (Date("2014-01-05"), Name("Bob"),   Addr(Some(5))),
         (Date("2014-01-05"), Name("Bob"),   Addr(Some(5))),
         (Date("2014-01-07"), Name("Daan"),  Addr(None)),
         (Date("2014-01-08"), Name("Bob"),   Addr(Some(6))),
         (Date("2014-01-08"), Name("Daan"),  Addr(Some(6))),
         (Date("2014-01-09"), Name("Chuck"), Addr(Some(2))),
         (Date("2014-01-10"), Name("Chuck"), Addr(Some(7))))

  println(localApp.eval(Site0(db)))
}
