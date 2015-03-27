package phant

import scala.language.higherKinds
import utils.illTyped

case class Guard[-S1,S2,+A](run: S1 => (A, S2)) {
  def flatMap[S3,B](f: A => Guard[S2,S3,B]): Guard[S1,S3,B] = Guard(
    (s1: S1) => {
      val (a, s2) = this.run(s1)
      f(a).run(s2)
    })

  def map[B](f: A => B): Guard[S1,S2,B] =
     this flatMap { a => Guard.unit(f(a)) }

//  def filter(p: A => Guard[S1,S2,Bool]): Guard[S
}

object Guard  {
  // State is splitable onto S1, S2
  case class Atom[S1,S2](s1: S1, s2: S2)
  type HEq[R]

  def unit[S,A](a: A): Guard[S,S,A] =
    Guard(s => (a, s))

  def crypt[S,P[_]]: Guard[S,P[S],Unit] = ???
  def cryptHEq[S]: Guard[S,HEq[S],Unit] = ???

  def decrypt[P[_], S]: Guard[P[S], S, Unit] = ???

  def frag[S1,S2]: Guard[Atom[S1,S2], (S1,S2), Unit] =
    Guard(s => ((), (s.s1, s.s2)))

  def defrag[S1,S2]: Guard[(S1,S2), Atom[S1,S2], Unit] =
    Guard({ case (s1, s2) => ((), Atom(s1, s2)) })

  // At start left is S1 and right is S2
  // After left is S3 and right is S2
  def onLFrag[S1,S2,S3,A](g: Guard[S1,S3,A]): Guard[(S1,S2),(S3,S2),A] = ???

  // At start left is S1 and right is S2
  // After left is S1 and right is S3
  def onRFrag[S1,S2,S3,A](g: Guard[S2,S3,A]): Guard[(S1,S2),(S1,S3),A] = ???

  def onFrag[S1,S2,S3,S4,A](gL: Guard[S1,S3,A],
                            gR: Guard[S2,S4,A]):
      Guard[(S1,S2), (S3,S4), A] =
    onLFrag[S1,S2,S3,A](gL) flatMap { _ => onRFrag[S3,S2,S4,A](gR) }
}

/** Monad hides the database and applies modification in place. */
object V1 {
  import Guard._

  (for {
     x <- unit[Unit, String]("abc")
     y <- unit(x + "def")
   } yield y) run (()): (String, Unit)


  (for {
     _ <- crypt[Unit, HEq]
     x <- unit("abc")
     y <- unit(x + "def")
   } yield y) run (()): (String, HEq[Unit])

  unit("abc") flatMap { s =>
    crypt[Unit, HEq] flatMap { _ =>
      unit("def") map     { d => s + d }: Guard[HEq[Unit], HEq[Unit], String]
    }: Guard[Unit, HEq[Unit], String]
  }: Guard[Unit, HEq[Unit], String]

  (for {
     _ <- crypt[Unit, HEq]
     x <- unit[HEq[Unit], String]("abc")
     _ <- decrypt[HEq, Unit]
     y <- unit(x + "def")
   } yield y) run (()): (String, Unit)

  (for {
     _ <- crypt[Unit, HEq]
     _ <- crypt[HEq[Unit], HEq]
     x <- unit("abc")
     y <- unit(x + "def")
   } yield y) run (()): (String, HEq[HEq[Unit]])

  (for {
     x <- unit("abc")
     _ <- frag[Unit, Unit]
     y <- unit(x + "def")
   } yield y) run (Atom((),())): (String, (Unit, Unit))

  (for {
     x <- unit("abc")
     _ <- frag[Unit, Unit]
     y <- unit(x + "def")
     _ <- defrag
   } yield y) run (Atom((),())): (String, Atom[Unit,Unit])

  (for {
     x <- unit("abc")
     _ <- frag[Unit, Unit]
     _ <- onLFrag(crypt[Unit, HEq])
     z <- unit(x + "def")
     _ <- defrag
   } yield z) run (Atom((),())): (String, Atom[HEq[Unit],Unit])

  (for {
     x <- unit("abc")
     _ <- frag[Unit, Unit]
     _ <- onLFrag(for {
                    _ <- crypt[Unit, HEq]
                    _ <- crypt[HEq[Unit], HEq]
                  } yield ())
     z <- unit(x + "def")
     _ <- defrag
   } yield z) run (Atom(Unit,Unit)): (String, Atom[HEq[HEq[Unit]], Unit])

  (for {
     x <- unit("abc")
     _ <- frag[Unit, Unit]
     _ <- onLFrag(for {
                    _ <- crypt[Unit, HEq]
                    _ <- crypt[HEq[Unit], HEq]
                  } yield ())
     z <- unit(x + "def")
     _ <- defrag
   } yield z) run (Atom(Unit,Unit)): (String, Atom[HEq[HEq[Unit]], Unit])

  (for {
     x <- unit("abc")
     _ <- frag[Unit, Unit]
     y <- onLFrag(for {
                    _ <- crypt[Unit, HEq]
                    _ <- crypt[HEq[Unit], HEq]
                    s <- unit("def")
                  } yield s)
     z <- unit(x + y + "ghi")
   } yield y) run (Atom(Unit,Unit)): (String, (HEq[HEq[Unit]], Unit))

  (for {
     x <- unit("abc")
     _ <- frag[Atom[Unit,Unit], Unit]
     _ <- onLFrag(for {
                    _ <- frag[Unit, Unit]
                    _ <- onLFrag(crypt[Unit, HEq])
                  } yield ())
     z <- unit(x + "def")
     _ <- defrag
   } yield z) run (Atom((Atom((),())),())): (String,
                                             Atom[(HEq[Unit],Unit), Unit])
}

/** Configuration combinator for a better type inference. */
object V2 {
  import Guard._

  def configure[S]: Guard[S,S,Unit] =
    Guard(s => ((), s))

  (for {
     _ <- configure[Unit]
     x <- unit("abc")
     y <- unit(x + "def")
   } yield y) run (()): (String, Unit)

  (for {
     _ <- configure[Unit]
     _ <- crypt[Unit, HEq]
     x <- unit("abc")
     y <- unit(x + "def")
   } yield y) run (()): (String, HEq[Unit])


  unit("abc") flatMap { s =>
    crypt[Unit, HEq] flatMap { _ =>
      unit("def") map     { d => s + d }: Guard[HEq[Unit], HEq[Unit], String]
    }: Guard[Unit, HEq[Unit], String]
  }: Guard[Unit, HEq[Unit], String]

  (for {
     _ <- configure[Unit]
     _ <- crypt[Unit, HEq]
     x <- unit[HEq[Unit], String]("abc")
     _ <- decrypt[HEq, Unit]
     y <- unit(x + "def")
   } yield y) run (()): (String, Unit)

  (for {
     _ <- configure[Unit]
     _ <- crypt[Unit, HEq]
     _ <- crypt[HEq[Unit], HEq]
     x <- unit("abc")
     y <- unit(x + "def")
   } yield y) run (()): (String, HEq[HEq[Unit]])

  (for {
     _ <- configure[Atom[Unit,Unit]]
     x <- unit("abc")
     _ <- frag
     y <- unit(x + "def")
   } yield y) run (Atom((),())): (String, (Unit, Unit))

  (for {
     _ <- configure[Atom[Unit,Unit]]
     x <- unit("abc")
     _ <- frag
     y <- unit(x + "def")
   } yield y) run (Atom((),())): (String, (Unit, Unit))

  (for {
     _ <- configure[Atom[Unit,Unit]]
     x <- unit("abc")
     _ <- frag
     y <- unit(x + "def")
     _ <- defrag
   } yield y) run (Atom((),())): (String, Atom[Unit,Unit])

  (for {
     _ <- configure[Atom[Unit,Unit]]
     x <- unit("abc")
     _ <- frag
     _ <- onLFrag(crypt[Unit, HEq])
     z <- unit(x + "def")
     _ <- defrag
   } yield z) run (Atom((),())): (String, Atom[HEq[Unit],Unit])

  (for {
     _ <- configure[Atom[Unit,Unit]]
     x <- unit("abc")
     _ <- frag
     _ <- onLFrag(for {
                    _ <- crypt[Unit, HEq]
                    _ <- crypt[HEq[Unit], HEq]
                  } yield ())
     z <- unit(x + "def")
     _ <- defrag
   } yield z) run (Atom(Unit,Unit)): (String, Atom[HEq[HEq[Unit]], Unit])

  (for {
     _ <- configure[Atom[Unit,Unit]]
     x <- unit("abc")
     _ <- frag
     _ <- onLFrag(for {
                    _ <- crypt[Unit, HEq]
                    _ <- crypt[HEq[Unit], HEq]
                  } yield ())
     z <- unit(x + "def")
     _ <- defrag
   } yield z) run (Atom(Unit,Unit)): (String, Atom[HEq[HEq[Unit]], Unit])

  (for {
     _ <- configure[Atom[Unit,Unit]]
     x <- unit("abc")
     _ <- frag
     y <- onLFrag(for {
                    _ <- crypt[Unit, HEq]
                    _ <- crypt[HEq[Unit], HEq]
                    s <- unit("def")
                  } yield s)
     z <- unit(x + y + "ghi")
   } yield y) run (Atom(Unit,Unit)): (String, (HEq[HEq[Unit]], Unit))
}

/** Let's be more specific with a concret example. */
object V3 {
  import Guard._
  import V2.configure

  // Library for type classes
  import spire.algebra._, spire.implicits._

  // TODO:
  // case class N (get: String)

  type D     = String
  type N     = String
  type A     = Option[Int]
  type Id    = Int
  type DB[X] = List[X]

  val db: DB[(D,N,A)] =
    List(("2014-01-01", "Bob",   Some(1)),
         ("2014-01-02", "Chuck", Some(2)),
         ("2014-01-03", "Bob",   Some(3)),
         ("2014-01-04", "Chuck", Some(4)),
         ("2014-01-05", "Bob",   Some(5)),
         ("2014-01-05", "Bob",   Some(5)),
         ("2014-01-07", "Daan",  None),
         ("2014-01-08", "Bob",   Some(6)),
         ("2014-01-08", "Daan",  Some(6)),
         ("2014-01-09", "Chuck", Some(2)),
         ("2014-01-10", "Chuck", Some(7)))

  // The get combinator offers a view on the database and enables
  // calculation on that view without modifying the database itself.
  def get[S]: Guard[S,S,S] =
    Guard(s => (s,s))

  def project[T,R](db: DB[T])(f: T => R): DB[R] =
    db map f

  def select[T](db: DB[T])(f: T => Boolean): DB[T] =
    db filter f

  // `g` is the reducer of a grp
  def groupby[T,R1: Eq,R2](db: DB[T])(f: T => R1)(g: DB[T] => R2): DB[R2] = {
    def mkGroup(db: DB[T]): DB[DB[T]] = db match {
      case Nil => Nil
      case line :: db =>
        (line :: db.filter(f(_) === f(line))) ::
          mkGroup(db.filter(f(_) =!= f(line)))
    }

    mkGroup(db) map g
  }

  // Sort on `<`
  def sort[T,R: Order](db: DB[T])(f: T => R): DB[T] =
    db.sortWith(f(_) < f(_))

  // -------------------------------------------- Most visited clients
  // Scenario that works only on one fragment after fragmentation.

  // No security, Centralized version
  for {
    _  <- configure[DB[(D,N,A)]]
    v1 <- get[DB[(D,N,A)]]
    // Projection that only keeps (N,A)
    v2 = project (v1) { case (_, n, a) => (n, a) }
    // Selection that returns lines with "Bob" and "Chuck"
    v3 = select (v2) {
      // Has an Eq constraint on N
      case (n, _) => List("Bob", "Chuck") exists (_ === n)
    }
    // Grouping on `n` and reduce that count, Has an Eq constraint
    v4 = groupby (v3) { case (n, _) => n } { grp =>
      (grp.head._1, grp.foldRight (0) { case ((n, _), rest) => 1 + rest })
    }
    // Sort on name
    v5 = sort(v4) { case (n, _) => n }
  } yield ()

  // Fragmentation
  import shapeless.Nat._

  def frag[D,N,A](n: _1): Guard[DB[(D,N,A)],
                                (DB[(D,Id)], DB[(N,A,Id)]),
                                Unit] =
    Guard(db => ((), (db.zipWithIndex.map {
                        case ((d,_,_), v) => (d, v)
                      },
                      (db.zipWithIndex.map {
                         case ((_,n,a), v) => (n, a, v)
                       }))))

  for {
    _  <- configure[DB[(D,N,A)]]
    // Fragmentation on the first column
    _  <- frag(_1)
    v1 <- get[(_, DB[(N,A,Id)])]
    // Note: Projection on v1 is now useless!
    // v2 = project (v1) { case (d, n, a) => (n, a) }
    v2 = v1._2
    // Note: Selection should now take into account index
    v3 = select (v2) {
      case (n, _, _) => List("Bob", "Chuck") exists (_ === n)
    }
    // Note: GroupBy should now take into account index
    v4 = groupby (v3) { case (n, _, _) => n } {grp =>
      (grp.head._1, grp.foldRight (0) { case ((n, _, _), rest) => 1 + rest })
    }
    // Note: No special case to handle for sort
    v5 = sort(v4) { case (n, _) => n }
  } yield ()

  // Fragmentation + Homomorphic Order
  trait Protection
  trait HES[R] extends Protection { def get: R }
  class HEq[R: Eq](val get: R) extends HES[R]
  object HEq {
    def apply[R: Eq](r: R) = new HEq(r)

    implicit def heq[R: Eq]: Eq[HEq[R]] = new Eq[HEq[R]] {
      override def eqv(x: HEq[R], y: HEq[R]) =
        implicitly[Eq[R]].eqv(x.get, y.get)
    }
  }
  class HOrder[R: Order](get: R) extends HEq[R](get)
  object HOrder {
    def apply[R: Order](r: R) = new HOrder(r)

    implicit def horder[R: Order]: Order[HOrder[R]] =
      new Order[HOrder[R]] {
        override def compare(x: HOrder[R], y: HOrder[R]) =
          implicitly[Order[R]].compare(x.get, y.get)
      }
  }

  def crypt[H[_] <: Protection,N,A,Id](n: _1)(f: N => H[N]):
      Guard[DB[(N,A,Id)], DB[(H[N], A, Id)], Unit] =
    Guard(db => ((), db.map { case (n, a, id) => (f(n), a, id) }))

  def cryptHOrder[N: Order,A,Id](n: _1): Guard[DB[(N,A,Id)], DB[(HOrder[N], A, Id)], Unit] =
    crypt(n)(n => HOrder(n))

  for {
    _  <- configure[DB[(D,N,A)]]
    _  <- frag(_1)
    // Encryption with Homomorphic Order on the first column of the
    // second fragment.
    _  <- onRFrag(cryptHOrder[N,A,Id](_1))
    v1 <- get[(_, DB[(HOrder[N],A,Id)])]
    v2 = v1._2
    // Note: OK with Homomorphic Order
    v3 = select (v2) {
      case (n, _, _) => List(HEq("Bob"), HEq("Chuck")) exists (_ === n)
    }
    // Note: OK with Homomorphic Order
    v4 = groupby (v3) { case (n, _, _) => n } {grp =>
      (grp.head._1, grp.foldRight (0) { case ((n, _, _), rest) => 1 + rest })
    }
    // Note: OK with Homorphic Order
    v5 = sort(v4) { case (n, _) => n }
  } yield ()

  // Fragmentation + Homomorphic Eq
  def cryptHEq[N: Eq,A,Id](n: _1):
      Guard[DB[(N,A,Id)], DB[(HEq[N], A, Id)], Unit] =
    crypt(n)(n => HEq(n))

  illTyped("""
  for {
    _  <- configure[DB[(D,N,A)]]
    _  <- frag(_1)
    // Encryption with Homomorphic Eq on the first column of the
    // second fragment.
    _  <- onRFrag(cryptHEq[N,A,Id](_1))
    v1 <- get[(_, DB[(HEq[N],A,Id)])]
    v2 = v1._2
    // Note: OK with Homomorphic Eq
    v3 = select (v2) {
      case (n, a, i) => List(HEq("Bob"), HEq("Chuck")) exists (_ === n)
    }
    // Note: OK with Homomorphic Eq
    v4 = groupby (v3) { case (n, _, _) => n } {grp =>
      (grp.head._1, grp.foldRight (0) { case ((n, _, _), rest) => 1 + rest })
    }
    // Note: Doesn't type check, there is no `<` on HEq
    v5 = sort(v4) { case (n, _) => n }
  } yield ()
  """)

  // Fragmentation + Homorphic Eq => Homorphic Order
  for {
    _  <- configure[DB[(D,N,A)]]
    _  <- frag(_1)
    // Encryption with Homomorphic Eq on the first column of the
    // second fragment.
    _  <- onRFrag(cryptHEq[N,A,Id](_1))
    v1 <- get[(_, DB[(HEq[N],A,Id)])]
    v2 = v1._2
    // Note: OK with Homomorphic Eq
    v3 = select (v2) {
      case (n, a, i) => List(HEq("Bob"), HEq("Chuck")) exists (_ === n)
    }
    // Note: OK with Homomorphic Eq
    v4: DB[(HEq[N],Int)] = groupby (v3) { case (n, _, _) => n } {grp =>
      (grp.head._1, grp.foldRight (0) { case ((n, _, _), rest) => 1 + rest })
    }
    // Note: We transform HEq into HOrder
    v5: DB[(HOrder[N],Int)] = v4.map {
      case (heqN, i) => (HOrder(heqN.get), i)
    }
    v6 = sort(v5) { case (n, _) => n }
  } yield ()

  // Fragmentation + Homorphic Eq => Pull
  case class Pull[R: Order](get: R) extends Protection
  implicit def pull[R: Order]: Order[Pull[R]] =
    new Order[Pull[R]] {
      override def compare(x: Pull[R], y: Pull[R]) =
        implicitly[Order[R]].compare(x.get, y.get)
  }

  for {
    _  <- configure[DB[(D,N,A)]]
    _  <- frag(_1)
    // Encryption with Homomorphic Eq on the first column of the
    // second fragment.
    _  <- onRFrag(cryptHEq[N,A,Id](_1))
    v1 <- get[(_, DB[(HEq[N],A,Id)])]
    v2 = v1._2
    // Note: OK with Homomorphic Eq
    v3 = select (v2) {
      case (n, a, i) => List(HEq("Bob"), HEq("Chuck")) exists (_ === n)
    }
    // Note: OK with Homomorphic Eq
    v4: DB[(HEq[N],Int)] = groupby (v3) { case (n, _, _) => n } {grp =>
      (grp.head._1, grp.foldRight (0) { case ((n, _, _), rest) => 1 + rest })
    }
    // Note: We pull data, what does it means for the rest of the
    // computation.
    v5: DB[(Pull[N],Int)] = v4.map { case (heqN, i) => (Pull(heqN.get), i) }
    v6 = sort(v5) { case (n, _) => n }
  } yield ()

  // -------------------------------------------- Most visited clients
  // Scenario that works on two fragment

  // Cenralized version
  for {
    // Configuration of the system with the database:
    _  <- configure[DB[(D,N,A)]]
    // Get a view on that database for futur calculations
    v1 <- get[DB[(D,N,A)]]
    // Projection that only keeps `d` and `n`
    v2 = project(v1) { case (d, n, a) => (d, n) }
    // Selection that only keeps "Bob" and "Chuck" entries
    v3 = select(v2) {
       case (d, n) => List("Chuck", "Bob") exists { _ == n }
    }
    // Grouping on `(d, n)` and reduce that count number of lines, Has
    // an Eq constraint
    v4 = groupby (v3) { case (d, n) => (d, n) } {grp =>
      (grp.head._1,
       grp.head._2,
       grp.foldRight (0) { case ((_, _), rest) => 1 + rest })
    }
    // Sort on name
    v5 = sort(v4) { case (d, n, _) => (d, n) }
  } yield ()

  // Fragmentation
  def join[D,N,Id](f1: DB[(D, Id)], f2: DB[(N, Id)]): DB[(D, N, Id)] =
    for {
      (x, i) <- f1
      (y, j) <- f2
      if i == j
    } yield (x, y, i)

  for {
    _   <- configure[DB[(D,N,A)]]
    _   <- frag(_1)
    v1  <- get[(DB[(D,Id)], DB[(N,A,Id)])]
    // Note: Projection works on the two fragments, but is useless
    // on frag1. Moreover, projection should take care of the index.
    // v2 = project(v1) { case (d, n, a) => (d, n) }
    v21 = v1._1
    v22 = project(v1._2) { case (n, _, i) => (n, i) }
    // Note: Selection works on the two fragments, but is useless on
    // frag1. Moreover, projection should take care of the index.
    v31 = v21
    v32 = select(v22) {
       case (n, _) => List("Chuck", "Bob") exists { _ == n }
    }
    // Note: Grouping on `(d,n)` requires joining fragments
    v4 = join(v31, v32)
    v5 = groupby (v4) { case (d, n, _) => (d, n) } {grp =>
      (grp.head._1,
       grp.head._2,
       grp.foldRight (0) { case ((_, _, _), rest) => 1 + rest })
    }
    v6 = sort(v5) { case (d, n, _) => (d, n) }
    _ <- unit(println(v6))
  } yield ()

  /*
  // FIXME: Here is the traduction of the previous for/yield. I don't
  // know why but the last `map` makes stuck the type inference. The
  // second implementation without the last map works infers
  // correclty.
  // Guard[DB[(D,N,A)],DB[(D,N,A)],DB[(String, Option[String])]]
  configure[DB[(D,N,A)]].flatMap({ _ =>
    get[DB[(D,N,A)]].map({ (v1: DB[(D,N,A)]) => {
                         val v2 = project(v1) { case (d, n, a) => (d, n) }
                         val v3 = select(v2) {
                           case (d, n) => List("Chuck", "Bob") exists { _ == n }
                         }
                         v3
                       // Guard[DB[(D,N,A)], DB[(D,N,A)], DB[(String, Option[String])]]
                       }}).map({ case (v4: DB[(String, Option[String])]) => v4 })
    })

  configure[DB[(D,N,A)]] flatMap({ _ =>
  get                        map({ v1 => {
               val v2 = project(v1) { case (d, n, a) => (d, n) }
               val v3 = select(v2) {
                 case (d, n) => List("Chuck", "Bob") exists { _ == n }
               }
               v3
             }})})

  // The correct traduction according to the spec is the following.
  // http://www.scala-lang.org/files/archive/spec/2.11/06-expressions.html#for-comprehensions-and-for-loops
  // I'm not sure of what happening there, If I follow the spec, then
  // type should be well inferred!? See step4 that compiles without
  // giving type information in `get`
  Step1:
  configure[DB[(D,N,A)]]
    .flatMap ({
                case _ =>
                  for {
                    v1 <- get[DB[(D,N,A)]]
                    v2 = project(v1) { case (d, n, a) => (d, n) }
                    v3 = select(v2) {
                      case (d, n) => List("Chuck", "Bob") exists { _ == n }
                    }
                  } yield v3
              })

  // Step2:
  configure[DB[(D,N,A)]]
    .flatMap ({
               case _ =>
                 for {
                   (v1, v2, v3) <- for (
                     x$1@v1 <- get[DB[(D,N,A)]]
                   ) yield {
                     val x$2@v2 = project(v1) { case (d, n, a) => (d, n) }
                     val x$3@v3 = select(v2) {
                       case (d, n) => List("Chuck", "Bob") exists { _ == n }
                     }
                     (x$1, x$2, x$3)
                   }
                 } yield v3
             })

  // Step3
  configure[DB[(D,N,A)]]
    .flatMap ({
               case _ =>
                  (for (x$1@v1 <- get[DB[(D,N,A)]])
                   yield {
                     val x$2@v2 = project(v1) { case (d, n, a) => (d, n) }
                     val x$3@v3 = select(v2) {
                       case (d, n) => List("Chuck", "Bob") exists { _ == n }
                     }
                     (x$1, x$2, x$3)
                   })
                    .map ({ case (v1, v2, v3) => v3 })
             })


  // Step4
  configure[DB[(D,N,A)]]
    .flatMap ({
               case _ =>
                  get
                    .map({ case x$1@v1 => {
                            val x$2@v2 = project(v1) { case (d, n, a) => (d, n) }
                            val x$3@v3 = select(v2) {
                              case (d, n) => List("Chuck", "Bob") exists { _ == n }
                            }
                            (x$1, x$2, x$3)
                          }})
              })
   // */
}

/** Add site to the implementation */
object V4 {
  import Guard._
  import V2.configure             // Monadic configure
  import V3.{db, D, N, A, Id, DB} // Some types
  import V3.get                   // Monadic get

  // Library for type classes
  import spire.algebra._, spire.implicits._

  trait Site[A, S[X]] {
    def get: A
    def apply[B](b: B): S[B]
    def move[S[A] <: Site[A,S]](f: A => S[A]): S[A] = f(get)
  }

  case class Site0[A](val get: A) extends Site[A,Site0] {
    def apply[B](b: B): Site0[B] = Site0(b)
  }

  case class Site1[A](val get: A) extends Site[A,Site1] {
    def apply[B](b: B): Site1[B] = Site1(b)
  }

  case class Site2[A](val get: A) extends Site[A,Site2] {
    def apply[B](b: B): Site2[B] = Site2(b)
  }

  // TODO: def receive = join + centralize

  object Site {
    def s0[A](a: A) = Site0(a)
    def s1[A](a: A) = Site1(a)
    def s2[A](a: A) = Site2(a)

    def map[Y,Z,S[X] <: Site[X,S]](s: S[DB[Y]])(f: Y => Z): S[DB[Z]] =
      s(s.get map f)

    def filter[Y,S[X] <: Site[X,S]](s: S[DB[Y]])(
      f: Y => Boolean): S[DB[Y]] =
      s(s.get filter f)

    def join[S[X] <: Site[X,S]](s1: S[DB[(String,Id)]],
                                s2: S[DB[(String,Id)]]):
        S[DB[(String,String,Id)]] =
      s1(for {
           (x, i) <- s1.get
           (y, j) <- s2.get
           if i == j
         } yield (x, y, i))

    def move[S1[X] <: Site[X,S1],
             S2[X] <: Site[X,S2], X](s1: S1[X])(
                                     f: X => S2[X]): S2[X] =
      s1.move(f)

    /** Moves at owner's site */
    def centralize[S[X] <: Site[X,S], X](s: S[X]): Site0[X] =
      s.move(Site.s0)
  }

  import Site._

  def _frag1(db: Site0[DB[(D,N,A)]]):
      (Site0[DB[(D,Id)]],
                         Site0[DB[(N,A,Id)]]) =
    (Site0(db.get.zipWithIndex.map {
             case ((d,_,_), v) => (d, v)
           }),
     (Site0(db.get.zipWithIndex.map {
              case ((_,n,a), v) => (n, a, v)
            })))

  def modify[S1,S2](f: S1 => S2): Guard[S1,S2,Unit] =
    Guard((s: S1) => ((), f(s)))

  def send[S[A] <: Site[A,S], A](f: A => S[A]):
      Guard[Site0[A], S[A], Unit] =
    Guard( db => ((), db.move(f) ))

  // TODO: Parametrer par les sites.
  def frag1: Guard[Site0[DB[(D,N,A)]],
                   (Site1[DB[(D,Id)]],
                    Site2[DB[(N,A,Id)]]),
                   Unit] =
    for {
      _ <- modify(_frag1)
      _ <- onLFrag(send[Site1, DB[(D,Id)]](s1))
      _ <- onRFrag(send[Site2, DB[(N,A,Id)]](s2))
    } yield ()

  // Add site is monad
  for {
    _ <- configure[Site0[DB[(D,N,A)]]]
    _ <- frag1 // frag1(s0,s2)
    d1 <- get[(Site1[DB[(D, Id)]],
               Site2[DB[(N, A, Id)]])]
    // Les sites sont implicites
    // d21 = d1._1 map ({ case (d,i) => (d,i) })
    d21 = map (d1._1) { case (d, i) => (d, i) }
    // d22 = d1._2 map ({ case (n,a,i) => (n,i) })
    d22 = map (d1._2) { case (n, a, i) => (n, i) }
    // d31 = d22 filter ({case (n,i) =>
    //                     DB("Chuck", "Bob").exists({ _ === n }) })
    d32 = filter(d22) { case (n, i) =>
      List("Bob", "Chuck") exists { _ === n }
    }
    // d32 = unFrag1(d21,d31)
    // d4  = join(d21,d32) // Doesn't type check
    d4 = join(move(d21)(s0), move(d32)(s0))
    // FIXME: following also type checks!
    // d321 = join(d21, d31.move(s1))
    // d322 = join(d21.move(s2), d31)
  } yield d4

  for {
    _ <- configure[Site0[DB[(D,N,A)]]]
    _ <- frag1 // frag1(s0,s2)
    d1 <- get[(Site1[DB[(D, Id)]],
               Site2[DB[(N, A, Id)]])]
    // Les sites sont implicites
    // d21 = d1._1 map ({ case (d,i) => (d,i) })
    d21 = map (d1._1) { case (d, i) => (d, i) }
    // d22 = d1._2 map ({ case (n,a,i) => (n,i) })
    d22 = map (d1._2) { case (n, a, i) => (n, i) }
    // d31 = d22 filter ({case (n,i) =>
    //                     DB("Chuck", "Bob").exists({ _ === n }) })
    d32 = filter(d22) { case (n, i) =>
      List("Bob", "Chuck") exists { _ === n }
    }
    // d32 = unFrag1(d21,d31)
    // d4  = join(d21,d32) // Doesn't type check
    // Note: Use centralize rather than move(*)(s0)
    d5 = join(centralize(d21), centralize(d32))
  } yield d5
}

/** A new Guard monad */
// -- Current --
object V5Current {
  type A = String
  type B = Option[Int]
  type Id = Int
  type DB[X] = List[X]
  import V3.{HEq, HOrder}          // Homomorphic Function

  // Library for type classes
  import spire.algebra._, spire.implicits._

  case class Guard2[-S1,S2,+A](run: S1 => (A, S2)) {
    def flatMap[S3,B](f: A => Guard2[S2,S3,B]): Guard2[S1,S3,B] = Guard2(
      (s1: S1) => {
        val (a, s2) = this.run(s1)
          f(a).run(s2)
      })

    def map[B](f: A => B): Guard2[S1,S2,B] =
      this flatMap { a => Guard2.unit(f(a)) }
  }

  object Guard2 {
    def unit[S,A](a: A): Guard2[S,S,A] =
      Guard2(s => (a, s))

    def configure[S]: Guard2[S,S,Unit] =
      Guard2(s => ((), s))

    // DB Shape Modifiers:
    def crypt1[P[_]]: Guard2[DB[(A,B)], DB[(P[A],B)], Unit] = ???
    def crypt2[P[_]]: Guard2[DB[(A,B)], DB[(A,P[B])], Unit] = ???

    def decrypt1[P[_]]: Guard2[DB[(P[A],B)], DB[(A,B)], Unit] = ???
    def decrypt2[P[_]]: Guard2[DB[(A,P[B])], DB[(A,B)], Unit] = ???

    def frag1[A,B]: Guard2[DB[(A,B)], (DB[(A,Id)], DB[(B,Id)]), Unit] = ???
    def defrag1[A,B]: Guard2[(DB[(A,Id)], DB[(B,Id)]), DB[(A,B)], Unit] = ???

    // DB query:
    def onDB[S,R](q: S => R): Guard2[S,S,R] =
      Guard2(s => (q(s), s))

    def onLFrag[SL,SR,R](q: SL => R): Guard2[(SL, SR), (SL, SR), R] =
      Guard2({ case s@(sl, _) => (q(sl), s) })

    def onRFrag[SL,SR,R](q: SR => R): Guard2[(SL, SR), (SL, SR), R] =
      Guard2({ case s@(_, sr) => (q(sr), s) })
  }

  // Query operations:
  // ------------------------------- Π
  // C ∈ P(T)
  def Π[T, C](db: DB[T])(p: T => C): DB[C] = db.map(p)

  def R[A,B]: ((A, B)) => ((A, B)) = identity
  def R1: ((A, B)) => A = _._1
  def R2[A,B]: ((A, B)) => B = _._2
  def Πlift(f: ((A,B)) => A)(
                implicit b: B): ((A,Id)) => ((A, Id)) = {
    case (a, id) => (f((a, b)), id)
  }
  def Πlift[A,B](f: ((A,B)) => B)(
                 implicit a: A): ((B,Id)) => ((B, Id)) = {
    case (b, id) => (f((a, b)), id)
  }
  def rmId[A,B](t: (A, B, Id)): (A, B) = (t._1, t._2)

  implicit val a: A = ""
  implicit val b: B = Some(0)

  // -------------------------------- σ
  def σ[T](db: DB[T])(p: T => Boolean): DB[T] = db.filter(p)

  def σlift[T](f: T => Boolean): ((T, Id)) => Boolean = {
    case (t, id) => f(t)
  }
  def ∧[A,B](f: A => Boolean, g: B => Boolean, h: ((A,B)) => Boolean):
      ((A,B)) => Boolean = {
    case (a, b) => f(a) && g(b) && h((a,b))
  }
  def f: A => Boolean = _ => true
  def g: B => Boolean = _ => true
  def g_heq: HEq[B] => Boolean = _ => true
  def h: ((A, B)) => Boolean = _ => true
  def h_heq: ((A, HEq[B])) => Boolean = _ => true

  // ------------------------------- γ
  // U ∈ P(T)
  def γ[T, U : Eq](db: DB[T])(p: T => U): DB[DB[T]] = db match {
    case Nil => Nil
    case line :: db =>
      (line :: db.filter(p(_) === p(line))) ::
        γ (db.filter(p(_) =!= p(line))) (p)
  }

  // Note: Use word receive or gather for centralize/join. Gather
  // means, brings data back. This works for defragmentation and
  // decryption of data. Thus, frag/defrag, crypt/decrypt are monadic
  // operations and gather (that works for both) is the value
  // operation. Gather is a downgrad operation at value level. Defrag
  // et Decrypt are downgrad operation at monadic level. See, A
  // library for Ligh-Weight Information Flow Securtity in Haskell.
  // *In a better definition, the gather should be a downgrade
  // operation that removes all security*.
  def gather[P[_]](db: DB[(P[A],B)]): DB[(A,B)] = ???
  def gather[P[_]](db: DB[(A,P[B])])(
                   implicit
                   $di: DummyImplicit): DB[(A,B)] = ???

  def gather(f1: DB[(A, Id)],
             f2: DB[(B, Id)]): DB[(A, B)] =
    for {
      (x, i) <- f1
      (y, j) <- f2
      if i == j
    } yield (x, y)

  def gather[P[_]](f1: DB[(P[A], Id)],
                   f2: DB[(B, Id)])(
                   implicit
                   $d: DummyImplicit): DB[(A,B)] = ???

  def gather[P[_]](f1: DB[(A, Id)],
                   f2: DB[(P[B], Id)])(
                   implicit
                   $d1: DummyImplicit,
                   $d2: DummyImplicit): DB[(A,B)] = ???

  import Guard2._

  // A centralized version.
  val abCentralized: Guard2[DB[(A,B)], DB[(A,B)], DB[(A,B)]] =
    (for {
       _ <- configure[DB[(A,B)]] // Database modifier doesn't have
                                 // identifier (type Unit)
       q <- onDB ((db: DB[(A,B)]) => { // Database accessor has
                                       // identifier (type query)
                    val r1 = Π (db) (R)
                    val r2 = σ (r1) (∧(f, g, h))
                    r2
                  })
     } yield q)


  // A fragmented version.
  val abFragmented: Guard2[DB[(A,B)], // The type is exactly the same as
                           DB[(A,B)], // Centralized version
                           DB[(A,B)]] =
    (for {
       _ <- configure[DB[(A,B)]] // Database modifier doesn't have
                                 // identifier (type Unit)
       _ <- crypt2[HEq]          // Monadic crypt
       _ <- frag1                // Monadic frag: frag really
                                 // distribute data, after frag I
                                 // cannot do things like crypt for
                                 // instance.
       q1 <- onLFrag ((lfrag: DB[(A, Id)]) => {
                        // Note: Lift that forgets `b` and takes in
                        // account `i`
                        val r1 = Π (lfrag) (Πlift(R1))
                        val r2 = σ (r1) (σlift(f))
                        r2
                      })
       q2 <- onRFrag ((rfrag: DB[(HEq[B],Id)]) => {
                        // Note: Lift that forgets `a` and takes in
                        // account `i`
                        val r1 = Π (rfrag) (Πlift(R2))
                        // Note: `g` is now heq
                        val r2 = σ (r1) (σlift(g_heq))
                        r2
                      })
       q5 = gather(q1, q2)  // gather is the query operation that copy
                            // two frags and join them at owner side
                            // and also decrypt crypted value.
       q  = σ (q5) (h)
       _ <- defrag1         // Defrag is the monadic operation that
                            // defrag the database
       _ <- decrypt2[HEq]   // Decrypt is the monadic operation that
                            // decrypt the database
     } yield q)

  // ---------------------------- Laws, from centralized to fragmented
  // In the following, we develop (as an equation) the pushing of
  // monadic defrag.
  // A fragmented version
  val abPushFrag_1: Guard2[DB[(A,B)], DB[(A,B)], DB[(A,B)]] =
    (for {
       _ <- configure[DB[(A,B)]]
       _ <- frag1
       _ <- defrag1
       q <- onDB ((db: DB[(A,B)]) => {
                    val r1 = Π (db) (R)
                    val r2 = σ (r1) (∧(f, g, h))
                    r2
                  })
     } yield q)

  val abPushFrag_2: Guard2[DB[(A,B)], DB[(A,B)], DB[(A,B)]] =
    (for {
       _  <- configure[DB[(A,B)]]
       _  <- frag1
       // r1
       q1 <- onLFrag { Π (_:DB[(A,Id)]) (Πlift(R1)) }
       q2 <- onRFrag { Π (_:DB[(B,Id)]) (Πlift(R2)) }
       _  <- defrag1 // Defrag traversing Π. Note: pushing defrag
                     // through a request produceq two requests that
                     // have to be gathered.
       r1 = gather(q1, q2)
       // r2
       q  <- onDB ((_:DB[(A,B)]) => {
                     val r2 = σ (r1) (∧(f, g, h))
                     r2
                   })
     } yield q)

  val abPushFrag_3: Guard2[DB[(A,B)], DB[(A,B)], DB[(A,B)]] =
    (for {
       _  <- configure[DB[(A,B)]]
       _  <- frag1
       // r1
       q1 <- onLFrag { Π (_:DB[(A,Id)]) (Πlift(R1)) }
       q2 <- onRFrag { Π (_:DB[(B,Id)]) (Πlift(R2)) }
       // r2
       q3 <- onLFrag { (_:DB[(A,Id)]) => σ (q1) (σlift(f)) }
       q4 <- onRFrag { (_:DB[(B,Id)]) => σ (q2) (σlift(g)) }
       _  <- defrag1 // Defrag traversing σ. Note: pushing defrag
                     // through a request produces two requests that
                     // have to be gathered.
       r1 = gather(q1, q2)
       r2 = gather(q3, q4)
       q = σ (r2) (h)
     } yield q)

  // --------------------------------- Laws, from decrypted to crypted
  // In the following, we develop (as an equation) the pushing of
  // monadic decrypt
  val abPushDecrypt_1: Guard2[DB[(A,B)], DB[(A,B)], DB[(A,B)]] =
    (for {
       _ <- configure[DB[(A,B)]]
       _ <- crypt2[HEq]
       _ <- decrypt2[HEq]
       q <- onDB ((db: DB[(A,B)]) => {
                    val r1 = Π (db) (R)
                    val r2 = σ (r1) (∧(f, g, h))
                    r2
                  })
     } yield q)

  val abPushDecrypt_2: Guard2[DB[(A,B)], DB[(A,B)], DB[(A,B)]] =
    (for {
       _  <- configure[DB[(A,B)]]
       _  <- crypt2[HEq]
       // r1
       q1 <- onDB { Π (_:DB[(A,HEq[B])]) (R) }
       _  <- decrypt2[HEq] // Decrypt traversing σ. Note: pushing
                           // decrypt through a request produces one
                           // query that has to be gathered.
       r1 =  gather(q1)
       q  <- onDB ((_:DB[(A,B)]) => {
                     val r2 = σ (r1) (∧(f, g, h))
                     r2
                   })
     } yield q)

  val abPushDecrypt_3: Guard2[DB[(A,B)], DB[(A,B)], DB[(A,B)]] =
    (for {
       _  <- configure[DB[(A,B)]]
       _  <- crypt2[HEq]
       // r1
       q1 <- onDB { Π (_:DB[(A,HEq[B])]) (R) }
       // r2
       q2 <- onDB { (_:DB[(A,HEq[B])]) => σ (q1) (∧(f, g_heq, h_heq)) }
       _  <- decrypt2[HEq]  // Decrypt traversing σ. Note: pushing
                            // decrypt through a request produces one
                            // query that has to be gathered.
       r1 =  gather(q1)
       r2 =  gather(q2)
       q = r2
     } yield q)
}

// -- Expected --

/*
object V5 {
  // TODO: Use word receive or gather for centralize/join. Gather
  // means, brings data back. This works for defragmentation and
  // decryption of data. Thus, frag/defrag, crypt/decrypt are monadic
  // operations and gather (that works for both) is the value
  // operation.

  // A centralized version.
  val mostVisitedCentralized: Guard[Site0[DB[(D,N,A)]],
                                    Site0[DB[(D,N,A)]],
                                    Site0[DB[(D,N)]]] =
    (for {
       _ <- configure[Site0[DB[(D,N,A)]]] // Database modifier
                                          // doesn't have identifier
                                          // (type Unit)
       q <- onDB (db => {                 // Database accessor has identifier (type query)
                    r1 = map (db) { case (d,n,a)  => (d,n) }
                    r2 = filter (r1) { case (d,n) =>
                      List("Bob", "Chuck") exists { _ === n }
                    }
                  })
     } yield q)

  // A fragmented version
  val mostVisitedFragmented: Guard[Site0[DB[(D,N,A)]],
                                   Site0[DB[(D,N,A)]],
                                   Site0[DB[(D,N)]]] = // The type is
                                                       // exactly the
                                                       // same as
                                                       // Centralized
                                                       // version
    (for {
       _ <- configure[Site0[DB[(D,N,A)]]] // Database modifier
                                          // doesn't have identifier
                                          // (type Unit)
       _ <- crypt2[HEq]
       _ <- frag1(s1,s2) // frag really distribute data, after frag I
                         // cannot do things like crypt for instance.
       q1 <- onLFrag { map (_) { case (d, i) => (d, i) } }
       q2 <- onRFrag ( frag2 => {
                        r1 = map (frag2) { case (n, a, i) => (n, i) }
                        r2 = filter(r1) { case (n, i) =>
                          List("Bob", "Chuck") exists { _ == n }
                        }
                      })
       v = illTyped("""q3 = join(q1, q2) // Doesn't type check""")
       q3 = centralize(q1)
       q4 = centralize(q2)
       q5 = join(q3, q4)   // Join is the query operation that copy
                           // two frags and join them at owner side.
       q6 = decrypt2[HEq](q5) // Decrypt is the query operation that
                              // decrypt value.
       _ <- defrag         // Defrag is the monadic operation that
                           // defrag the database
       _ <- decrypt2[HEq]  // Decrypt is the monadic operation that
                           // decrypt the database
     } yield q6)

  // ---------------------------- Laws, from centralized to fragmented
  // In the following, we develop (as an equation) the pushing of
  // monadic defrag.
  val mostVisitedPushDefrag_1: Guard[Site0[DB[(D,N,A)]],
                                     Site0[DB[(D,N,A)]],
                                     Site0[DB[(D,N)]]] =
    (for {
       _ <- configure[Site0[DB[(D,N,A)]]]
       _ <- frag1(s1,s2) // Monadic frag
       _ <- defrag       // Monadic defrag
       q <- onDB (db => {
                    r1 = map (db) { case (d,n,a)  => (d,n) }
                    r2 = filter (r1) { case (d,n) =>
                      List("Bob", "Chuck") exists { _ === n }
                    }
                  })
     } yield q)

  val mostVisitedPushDefrag_2: Guard[Site0[DB[(D,N,A)]],
                                     Site0[DB[(D,N,A)]],
                                     Site0[DB[(D,N)]]] =
    (for {
       _  <- configure[Site0[DB[(D,N,A)]]]
       _  <- frag1(s1,s2)
       // r1
       q1 <- onLFrag { map (_) { case (d, i) => (d, i) } }
       q2 <- onRFrag { map (_) { case (n, a, i) => (n, i) } }
       _  <- defrag // Defrag traversing Π. Note: pushing defrag
                    // through a request produce two requests that
                    // have to be centralize/join later.
       r1 = join(centralize(q1), centralize(q2))
       // q
       q  <- onDB (db => {
                     r2 = filter(r1) { case (d,n) =>
                       List("Bob", "Chuck") exists { _ === n }
                     }
                   })
     } yield q)

  val mostVisitedPushDefrag_3: Guard[Site0[DB[(D,N,A)]],
                                     Site0[DB[(D,N,A)]],
                                     Site0[DB[(D,N)]]] =
    (for {
       _  <- configure[Site0[DB[(D,N,A)]]]
       _  <- frag1(s1,s2)
       // r1
       q1 <- onLFrag { map (_) { case (d, i) => (d, i) } }
       q2 <- onRFrag { map (_) { case (n, a, i) => (n, i) } }
       // r2
       q3 <- onLFrag { q1 }
       q4 <- onRFrag (filter (q2) {
                        case (n, i) =>
                          List("Bob", "Chuck") exists { _ === n }
                      })
       _  <- defrag // Defrag traversing σ
       r1 = join(centralize(q1), centralize(q2))
       r2 = join(centralize(q3), centralize(q4))
       // q
       q  = r2
     } yield q)

  // --------------------------------- Laws, from decrypted to crypted
  // In the following, we develop (as an equation) the pushing of
  // monadic decrypt
  val mostVisitedPushDecrypt_1: Guard[Site0[DB[(D,N,A)]],
                                      Site0[DB[(D,N,A)]],
                                      Site0[DB[(D,N)]]] =
    (for {
       _  <- configure[Site0[DB[(D,N,A)]]]
       _  <- crypt1[HEq]   // Monadic crypt
       _  <- decrypt1[HEq] // Monadic decrypt
       q  <- onDB (db => {
                     r1 = map (db) { case (d,n,a)  => (d,n) }
                     r2 = filter (r1) { case (d,n) =>
                       List("Bob", "Chuck") exists { _ === n }
                     }
                   })
     } yield q)

  val mostVisitedPushDecrypt_2: Guard[Site0[DB[(D,N,A)]],
                                      Site0[DB[(D,N,A)]],
                                      Site0[DB[(D,N)]]] =
    (for {
       _ <- configure[Site0[DB[(D,N,A)]]]
       _ <- crypt1[HEq]
       // r1
       q1 <- onDB { map (_) { case (d,n,a)  => (d,n) } }
       _ <- decrypt1[HEq] // Decrypt traversing Π. Note: pushing
                          // decrypt through a request produce one
                          // request that has to be decrypt later.
       r1 = decrypt1[HEq](q1)
       // q
       q  <- onDB (db => {
                     r2 = filter (q1) { case (d,n) =>
                       List("Bob", "Chuck") exists { _ === n }
                     }
                   })
     } yield q)

  val mostVisitedPushDecrypt_3: Guard[Site0[DB[(D,N,A)]],
                                      Site0[DB[(D,N,A)]],
                                      Site0[DB[(D,N)]]] =
    (for {
       _ <- configure[Site0[DB[(D,N,A)]]]
       _ <- crypt1[HEq]
       // r1
       q1 <- onDB { map (_) { case (d,n,a)  => (d,n) } }
       // r2
       q2 <- onDB (_ => {
                    r2 = filter (q1) { case (d,n) =>
                      List(HEq("Bob"), HEq("Chuck")) exists { _ === n }
                    }
                  })
       _ <- decrypt1[HEq] // Decrypt traversing σ
       r1 = decrypt1[HEq](q1)
       r2 = decrypt1[HEq](q2)
       // q
       q = r2
     } yield q)

  // Composition
  val toto = for {
    q <- mostVisited
    // ...
  } yield q
}

//  // ----------- Laws
//  _  <- decrypt
//  qi = decrypt(qi)
//  q <- Π

//  q <- Π
//  _  <- decrypt
//  qi = decrypt(qi)
//  q = decrypt(q)

// //----------
//  _ <- crypt[HEq]
//    ...
//  _ <- decrypt[HEq]
//  qi = decrypt(qi)
//  q <- σ (qj) // j in i

//  _ <- crypt[HEq]
//    ...
//  q <- σ[Heq]
//  _ <- decrypt
//  qi = decrypt(qi)
//  q = decrypt(q)




// val mostVisited =
//   (for {
//      _ <- configure[Site0[DB[(D,N,A)]]]
//      _ <- frag1(s1,s2)
//      // Prend les deux frag, fait une copie locale, joint les deux
//      // frags et appelle la fonction. Guard[(S1,S2), (S1,S2), S1 ++ S2]
//      q <- defrag (db => {
//                     r1 = map (db) { case (d,n,a)  => (d,n) }
//                     r2 = filter(r1) { case (d,n) =>
//                       List("Bob", "Chuck") exists { _ === n }
//                     }
//                   })

//      // ...
//      q <- onDB (db => {
//                   r1 = map (db) { case (d,n,a)  => (d,n) }
//                   // defrag
//                   r2 = filter(r1) { case (d,n) =>
//                     List("Bob", "Chuck") exists { _ === n }
//                   }
//                 })

//      // r1
//      q1 <- onLFrag { map (_) { case (d, i) => (d, i) } }
//      q2 <- onRFrag { map (_) { case (n, a, i) => (n, i) } }

//      q3 = filter (q2) { case (n, i) =>
//        List("Bob", "Chuck") exists { _ === n }
//      }
//    } yield q)


// */
