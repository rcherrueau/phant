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
            R2[C2] <: Rsc,
            R3[C3] <: Rsc,
            PT[C1] <: Protected](
    n: _1)(
    f: C1 => PT[C1]): Guard3[S[DB[(Raw[C1], R2[C2], R3[C3])]],
                             S[DB[(PT[C1], R2[C2], R3[C3])]],
                             Unit] =
    State.iModify(s => s(s.get map { case (c1, c2, c3) => (f(c1.get), c2, c3) }))

  /** Encrypts the second column of the DB. */
  def crypt[C1,C2,C3,
            S[X] <: Site[X,S],
            R1[C1] <: Rsc,
            R3[C3] <: Rsc,
            PT[C2] <: Protected](
    n: _2)(
    f: C2 => PT[C2])(
    implicit
    $dm: DummyImplicit): Guard3[S[DB[(R1[C1], Raw[C2], R3[C3])]],
                                S[DB[(R1[C1], PT[C2], R3[C3])]],
                                Unit] =
    State.iModify(s => s(s.get map { case (c1, c2, c3) => (c1, f(c2.get), c3) }))

  /** Encrypts the third column of the DB. */
  def crypt[C1,C2,C3,
            S[X] <: Site[X,S],
            R1[C1] <: Rsc,
            R2[C2] <: Rsc,
            PT[C3] <: Protected](
    n: _3)(
    f: C3 => PT[C3])(
    implicit
    $dm1: DummyImplicit,
    $dm2: DummyImplicit): Guard3[S[DB[(R1[C1], R2[C2], Raw[C3])]],
                                 S[DB[(R1[C1], R2[C2], PT[C3])]],
                                 Unit] =
    State.iModify(s => s(s.get map { case (c1, c2, c3) => (c1, c2, f(c3.get)) }))

  /** Decrypts the first column of the DB. */
  def decrypt[C1,C2,C3,
              S[X] <: Site[X,S],
              R2[C2] <: Rsc,
              R3[C3] <: Rsc,
              PT[C1] <: Protected](
    n: _1)(
    f: PT[C1] => C1): Guard3[S[DB[(PT[C1], R2[C2], R3[C3])]],
                             S[DB[(Raw[C1], R2[C2], R3[C3])]],
                             Unit] =
    State.iModify(s => s(s.get map { case (c1, c2, c3) => (Raw(f(c1)), c2, c3) }))

  /** Decrypts the second column of the DB. */
  def decrypt[C1,C2,C3,
            S[X] <: Site[X,S],
            R1[C1] <: Rsc,
            R3[C3] <: Rsc,
            PT[C2] <: Protected](
    n: _2)(
    f: PT[C2] => C2)(
    implicit
    $dm: DummyImplicit): Guard3[S[DB[(R1[C1], PT[C2], R3[C3])]],
                                S[DB[(R1[C1], Raw[C2], R3[C3])]],
                                Unit] =
    State.iModify(s => s(s.get map { case (c1, c2, c3) => (c1, Raw(f(c2)), c3) }))

  /** Decrypts the third column of the DB. */
  def decrypt[C1,C2,C3,
              S[X] <: Site[X,S],
              R1[C1] <: Rsc,
              R2[C2] <: Rsc,
              PT[C3] <: Protected](
    n: _3)(
    f: PT[C3] => C3)(
    implicit
    $dm1: DummyImplicit,
    $dm2: DummyImplicit): Guard3[S[DB[(R1[C1], R2[C2], PT[C3])]],
                                 S[DB[(R1[C1], R2[C2], Raw[C3])]],
                                 Unit] =
    State.iModify(s => s(s.get map { case (c1, c2, c3) => (c1, c2, Raw(f(c3))) }))

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
    State.gets({ case (_, sr) => sr(q(sr.get)) })}


object DB {
  import spire.algebra._, spire.implicits._
  import Guard3.Idx

  type DB[X] = List[X]

  // implicit should have different names
  implicit def ΠR3toC1[C1,C2,C3](r: (Raw[C1], Raw[C2], Raw[C3])): Raw[C1] = r._1
  implicit def ΠR1IdxtoC1[C1](r: (Raw[C1], Idx)): Raw[C1] = r._1
  implicit def ΠR21IdxtoC2[C1,C2](r: (HEq[C1], Raw[C2], Idx)): Raw[C2] = r._2
  implicit def ΠR21IdxtoIdx[C1,C2](r: (HEq[C1], Raw[C2], Idx)): Idx = r._3

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

  def fold[T,Z](dbs: List[DB[T]])(z: Z)(f: (Z,T) => Z): DB[Z] =
    dbs.map{ _.foldLeft(z)(f) }

  def count[T](dbs: List[DB[T]]): DB[Int] =
    fold(dbs)(0)((z,r) => z+1)


  // Defrag Left Grouped
  def gather[C1,
             S1[X] <: Site[X,S1],
             S2[X] <: Site[X,S2]](fragL: S1[List[DB[(C1, Idx)]]],
                                  fragR: S2[DB[(Idx)]]):
      Site0[List[DB[(C1)]]] =
    Site0(
      fragL.get.map(db => for {
                      (x, i) <- db
                      (j) <- fragR.get
                      if i == j
                    } yield (x)))
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
           R3[Addr] <: Rsc](r: (R1[Date], R2[Name], R3[Addr])): (R1[Date]) = (r._1)

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
                       Site0[DB[Int]]] =
     for {
       _ <- configure[Date, Name, Addr]
       q <- query((db: DB[(Raw[Date], Raw[Name], Raw[Addr])]) => {
                    val r1 = σ (db) (lastweek)
                    val r2 = σ (r1) (atdesk)
                    val r3 = Π (r2) (date)
                    val r4 = group (r3) ({ case (d) => (d) })
                    val r5 = count (r4); r5
                  })
     } yield q

  val cloudApp: Guard3[Site0[DB[(Raw[Date], Raw[Name], Raw[Addr])]],
                       ( Site1[DB[(Raw[Date], Idx)]],
                         Site2[DB[(HEq[Name], Raw[Addr], Idx)]] ),
                       Site0[DB[Int]]] =
     for {
       _  <- configure[Date, Name, Addr]
       _  <- crypt (_2) (HEq(_:Name))
       _  <- fragV (_1) (Site.s1, Site.s2)
       qL <- queryL ((fragL: DB[(Raw[Date], Idx)]) => {
                       val r1 = σ (fragL) (lastweek)
                       val r2 = Π (r1) ({ case (d,i) => (d,i) })
                       val r3 = group (r2) ({ case (d,i) => (d) }); r3
                     })
       qR <- queryR ((fragR: DB[(HEq[Name], Raw[Addr], Idx)]) => {
                       val r1 = σ (fragR) (atdesk)
                       val r2 = Π (r1) ({ case (n,a,i) => (i) }); r2
                     }): Guard3[( Site1[DB[(Raw[Date], Idx)]],
                                  Site2[DB[(HEq[Name], Raw[Addr], Idx)]] ),
                                ( Site1[DB[(Raw[Date], Idx)]],
                                  Site2[DB[(HEq[Name], Raw[Addr], Idx)]] ),
                                Site2[DB[(Idx)]]]
       // FIXME: Who manages site on query? Is it monad of Site itself?
     } yield Site0(count (gather(qL, qR).get))

  val leftFirstApp: Guard3[Site0[DB[(Raw[Date], Raw[Name], Raw[Addr])]],
                           ( Site1[DB[(Raw[Date], Idx)]],
                             Site2[DB[(HEq[Name], Raw[Addr], Idx)]] ),
                           Site2[DB[Int]]] =
    for {
       _   <- configure[Date, Name, Addr]
       _   <- crypt (_2) (HEq(_:Name))
       _   <- fragV (_1) (Site.s1, Site.s2)
       ids <- queryL ((fragL: DB[(Raw[Date], Idx)]) => {
                       val r1 = σ (fragL) (lastweek)
                       val r2 = Π (r1) ({ case (d,i) => (i) }); r2
                     })
       q   <- queryR ((fragR: DB[(HEq[Name], Raw[Addr], Idx)]) => {
                        val r1 = σ (fragR) ((idx: Idx) =>
                          ids.get.exists(_ === idx))
                        val r2 = group (r1) ({ case (n,a,i) => (n) })
                        val r3 = count (r2); r3
                     })
    } yield q

  // val twiceEnc =
  //   for {
  //     _ <- configure[Date, Name, Addr]
  //     _ <- crypt (_2) (HEq(_:Name))
  //     _ <- crypt (_2) (HEq(_:Name))
  //   } yield ()

  // val unfragQueryOnFrag =
  //   for {
  //     _ <- configure[Date, Name, Addr]
  //     _ <- fragV (_1) (Site.s1, Site.s2)
  //     q <- query (db => { /* ... */ })
  //   } yield ()

  // val grpOnAES =
  //   for {
  //     _ <- configure[Date, Name, Addr]
  //     _ <- crypt (_2) (AES(_:Name))
  //     q <- query ((db: DB[(Raw[Date], AES[Name], Raw[Addr])]) => {
  //                   group (db) ({ case (d,n,a) => (n) })
  //                 })
  //   } yield ()

  val db: DB[(Raw[Date],Raw[Name],Raw[Addr])] =
   List((Raw(Date("2014-01-01")), Raw(Name("Bob")),   Raw(Addr(Some(1)))),
        (Raw(Date("2014-01-02")), Raw(Name("Chuck")), Raw(Addr(Some(2)))),
        (Raw(Date("2014-01-03")), Raw(Name("Bob")),   Raw(Addr(Some(3)))),
        (Raw(Date("2014-01-04")), Raw(Name("Chuck")), Raw(Addr(Some(4)))),
        (Raw(Date("2014-01-05")), Raw(Name("Bob")),   Raw(Addr(Some(5)))),
        (Raw(Date("2014-01-05")), Raw(Name("Bob")),   Raw(Addr(Some(5)))),
        (Raw(Date("2014-01-07")), Raw(Name("Daan")),  Raw(Addr(None))),
        (Raw(Date("2014-01-08")), Raw(Name("Bob")),   Raw(Addr(Some(6)))),
        (Raw(Date("2014-01-08")), Raw(Name("Daan")),  Raw(Addr(Some(6)))),
        (Raw(Date("2014-01-09")), Raw(Name("Chuck")), Raw(Addr(Some(2)))),
        (Raw(Date("2014-01-10")), Raw(Name("Chuck")), Raw(Addr(Some(7)))))

  println(localApp.eval(Site0(db)))
  println(cloudApp.eval(Site0(db)))
  println(leftFirstApp.eval(Site0(db)))
}
