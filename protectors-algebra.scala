package phant

import scala.language.higherKinds
import spire.algebra._
import spire.implicits._

case class Guard[-S1,S2,+A](run: S1 => (A, S2)) {
  def flatMap[S3,B](f: A => Guard[S2,S3,B]): Guard[S1,S3,B] = Guard(
    (s1: S1) => {
      val (a, s2) = this.run(s1)
      f(a).run(s2)
    })

  def map[B](f: A => B): Guard[S1,S2,B] =
     this flatMap { a => Guard.unit(f(a)) }
}

object Guard extends App {
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


  // (for {
  //    _ <- frag[_2]
  //    _ <- onLFrag(for {
  //                   _ <- crypt[Unit, HEq]
  //                 } yield ())
  //    z <- unit(x + "def")
  //    _ <- defrag
  //  } yield z) run (db): (String,
  //                                            Atom[(HEq[Unit],Unit), Unit])
}

/** Let's be more specific with a concret example. */
object V3 {
  import Guard._
  import V2.configure

  type Line = (String, Option[String], Int)
  type DB[X] = List[X]
  val db: DB[Line] =
    List(("2014-01-01", Some("Bob"),   1),
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

  // The get combinator offers a view on the database and enables
  // calculation on that view without modifying the database itself.
  def get[S]: Guard[S,S,S] =
    Guard(s => (s,s))

  def project[T,R](db: DB[T])(f: T => R): DB[R] =
    db map f

  def select[T](db: DB[T])(f: T => Boolean): DB[T] =
    db filter f

  // No security
  for {
    // Configuration of the system with the database:
    _  <- configure[DB[Line]]
    // Get a view on that database for futur calculations
    v1 <- get[DB[Line]]
    // Projection that only keeps `d` and `n`
    v2 = project(v1) { case (d, n, a) => (d, n) }
    // Selection that only keeps "Bob" and "Chuck" entries
    v3 = select(v2) {
       case (d, n) => List("Chuck", "Bob") exists { _ == n }
    }
  } yield v3

  // // FIXME: Here is the traduction of the previous for/yield. I don't
  // // know why but the last `map` makes stuck the type inference. The
  // // second implementation without the last map works infers
  // // correclty.
  // // Guard[DB[Line],DB[Line],DB[(String, Option[String])]]
  // configure[DB[Line]].flatMap({ _ =>
  //   get[DB[Line]].map({ (v1: DB[Line]) => {
  //                        val v2 = project(v1) { case (d, n, a) => (d, n) }
  //                        val v3 = select(v2) {
  //                          case (d, n) => List("Chuck", "Bob") exists { _ == n }
  //                        }
  //                        v3
  //                      // Guard[DB[Line], DB[Line], DB[(String, Option[String])]]
  //                      }}).map({ case (v4: DB[(String, Option[String])]) => v4 })
  //   })

  // configure[DB[Line]].flatMap({ _ =>
  //   get.map({ v1 => {
  //              val v2 = project(v1) { case (d, n, a) => (d, n) }
  //              val v3 = select(v2) {
  //                case (d, n) => List("Chuck", "Bob") exists { _ == n }
  //              }
  //              v3
  //                // Guard[DB[Line], DB[Line], DB[(String, Option[String])]]
  //            }})})

  // // The correct traduction according to the spec is the following.
  // // http://www.scala-lang.org/files/archive/spec/2.11/06-expressions.html#for-comprehensions-and-for-loops
  // // I'm not sure of what happening there, If I follow the spec, then
  // // type should be well inferred!? See step4 that compiles without
  // // giving type information in `get`
  // Step1:
  // configure[DB[Line]]
  //   .flatMap ({
  //               case _ =>
  //                 for {
  //                   v1 <- get[DB[Line]]
  //                   v2 = project(v1) { case (d, n, a) => (d, n) }
  //                   v3 = select(v2) {
  //                     case (d, n) => List("Chuck", "Bob") exists { _ == n }
  //                   }
  //                 } yield v3
  //             })

  // // Step2:
  // configure[DB[Line]]
  //   .flatMap ({
  //              case _ =>
  //                for {
  //                  (v1, v2, v3) <- for (
  //                    x$1@v1 <- get[DB[Line]]
  //                  ) yield {
  //                    val x$2@v2 = project(v1) { case (d, n, a) => (d, n) }
  //                    val x$3@v3 = select(v2) {
  //                      case (d, n) => List("Chuck", "Bob") exists { _ == n }
  //                    }
  //                    (x$1, x$2, x$3)
  //                  }
  //                } yield v3
  //            })

  // // Step3
  // configure[DB[Line]]
  //   .flatMap ({
  //              case _ =>
  //                 (for (x$1@v1 <- get[DB[Line]])
  //                  yield {
  //                    val x$2@v2 = project(v1) { case (d, n, a) => (d, n) }
  //                    val x$3@v3 = select(v2) {
  //                      case (d, n) => List("Chuck", "Bob") exists { _ == n }
  //                    }
  //                    (x$1, x$2, x$3)
  //                  })
  //                   .map ({ case (v1, v2, v3) => v3 })
  //            })


  // // Step4
  // configure[DB[Line]]
  //   .flatMap ({
  //              case _ =>
  //                 get
  //                   .map({ case x$1@v1 => {
  //                           val x$2@v2 = project(v1) { case (d, n, a) => (d, n) }
  //                           val x$3@v3 = select(v2) {
  //                             case (d, n) => List("Chuck", "Bob") exists { _ == n }
  //                           }
  //                           (x$1, x$2, x$3)
  //                         }})
  //             })


  import shapeless.Nat._
  type F1 = (String, Int)
  type F2 = (Option[String], Int, Int)

  def frag[N]: Guard[DB[Line], (DB[F1], DB[F2]), Unit] =
    Guard(db => ((), (db.zipWithIndex.map {
                        case ((d,_,_), v) => (d, v)
                      },
                      (db.zipWithIndex.map {
                         case ((_,n,a), v) => (n, a, v)
                       }))))
  def join(f1: DB[(String, Int)],
           f2: DB[(Option[String], Int)]): DB[(String, Option[String], Int)] =
    for {
      (x, i) <- f1
      (y, j) <- f2
      if i == j
    } yield (x, y, i)

  // With fragmentation
  for {
    _  <- configure[DB[Line]]
    _  <- frag[_1]
    v1 <- get[(DB[F1], DB[F2])]
    // v2 = project (v1) { case (d, n, a) => (d, n) }
    v21 = project (v1._1) { case (d, i) => (d, i) }
    v22 = project (v1._2) { case (n, a, i) => (n, i) }
    // v3 = select (v2) {
    //   case (d, n) => List("Chuck", "Bob") exists { _ == n }
    // }
    v31 = select (v22) {
      case (n, i) => List("Chuck", "Bob") exists { _ == n }
    }
    v32 = join(v21,v31)
   } yield v32

  def crypt[N,H[_]]: Guard[DB[F2], DB[(H[Option[String]], Int, Int)], Unit] = ???
  trait Protection { def get: String }
  trait Raw[R] extends Protection { def decode: R }
  type Pull[C] <: Protection
  type AES[R] <: Protection
  type HES <: Protection
  type HEq[R] <: HES
  type HOrder[R] <: HEq[R]

  // With fragmentation + Homomorphic Order
  for {
    _  <- configure[DB[Line]]
    _  <- frag[_1]
    _  <- onRFrag(crypt[_1, HOrder])
    v1 <- get[(DB[F1], DB[(HOrder[Option[String]], Int, Int)])]
    v21 = project (v1._1) { case (d, i) => (d, i) }
    v22 = project (v1._2) { case (n, a, i) => (n, i) }
    v31 = select (v22) {
      case (n, i) => List("Chuck", "Bob") exists { _ == n }
    }
    v32 = join(v21,v31)
   } yield v32
}
