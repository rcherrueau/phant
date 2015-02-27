package phant

import scala.language.higherKinds
import spire.algebra._
import spire.implicits._

import resources._
import ops.db._

import shapeless._


/*
monad Guard[P[R],A]
 return: A => Guard[P[R],A]
 bind: Guard[P[R]A] => (A => Guard[P[R],B]) => Guard[P[R],B]
 crypt: P => R => Guard[P[R],_] // put
 decrypt: P => Guard[P[R],R] // get
 modify: (R => R) => Guard[P[R],_]

String => List[(A, String)]
List[String => (A, String)]

Guard[P1[R],A] => Guard[P2[R],A] => Guard[P2[P1[R]],A]

frag: Int => DB => Guard[Frag[(DB.frag1, DB.frag2)],A]
join:

Guard[Frag[(DB.frag1, DB.frag2)],A]

// 1. Fragment,
// 2. chiffre AES (Symmetric) cols 1er frag
// 3. pull cols 2em frag chez owner.

frag1: Guard[DB.frag1,A] => Guard[Frag[(DB.frag1, DB.frag2)],A]

// 2 choix:
// 1. L'état représente l'évolution de la structure de la rsc.
// => Pile monadic ? Lift
// 2. Calcul monadic: le calcul représente l'évolution de la
//    structure de la rsc.
// =>

// Split state in two parts:
frag: Guard[P[(R1,R2)], Unit] => Guard[(P[R1],P[R2]), Unit]
frag: Guard[C[R1 F: R2], Unit] => Guard[C[R1] F: C[R2], Unit]

join: Guard[(P[R1],P[R2]), Unit] => Guard[P[(R1,R2)], Unit]

// Does some calculi on first frag
onFrag1: Guard[P[R1], Unit] => Guard[(P[R1],P[R2]), Unit]
*/

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

  def run[S,A](s: S): Guard[S,S,A] = ???

  def init[S]: Guard[S,S,S] =
    Guard(s => (s, s))

  def init[S](s: S): Guard[S,S,S] =
    Guard(s => (s, s))

  def get[S]: Guard[S,S,S] =
    Guard(s => (s,s))

  def unit[S,A](a: A): Guard[S,S,A] =
    Guard(s => (a, s))

  def crypt[S,P[_]]: Guard[S,P[S],Unit] = ???
  def cryptHEq[S]: Guard[S,HEq[S],Unit] = ???

  def decrypt[P[_], S]: Guard[P[S], S, Unit] = ???

  def frag[S1,S2]: Guard[Atom[S1,S2], (S1,S2), Unit] =
    Guard(s => ((), (s.s1, s.s2)))

  def frag1: Guard[List[(String,String,String)],
                   (List[(String,Int)],
                    List[(String,String,Int)]),
                   Unit] = Guard(db =>
                     ((), (db.zipWithIndex.map {
                                 case ((d,_,_), v) => (d, v)
                               },
                               db.zipWithIndex.map {
                                 case ((_,n,a), v) => (n, a, v)
                               })))


  def defrag[S1,S2]: Guard[(S1,S2), Atom[S1,S2], Unit] =
    Guard({ case (s1, s2) => ((), Atom(s1, s2)) })

  // FIXME:
  // Why run method doesn't drive the type inference here?
  // See http://pchiusano.blogspot.fr/2011/05/making-most-of-scalas-extremely-limited.html
  // See https://github.com/ljwagerfield/scala-type-inference
  // See http://stackoverflow.com/q/28679016/2072144
  import Nat._
  (for {
    _ <- init[String |: EOCol] flatMap { _ => fragDB(_1) }
    x <- unit("abc")
    y <- unit(x + "def")
  } yield y): Guard[String |: EOCol, (String |: EOCol, EOCol), _]

  def fragDB[S <: DB](n: Nat)(
                      implicit
                      tk: Taker[n.N, S],
                      dp: Dropper[n.N, S]): Guard[S, (tk.Out, dp.Out), Unit] = ???

  // At start right is S1 and left is S2
  // After right is S3 and left is S2
  def onRFrag[S1,S2,S3,A](g: Guard[S1,S3,A]): Guard[(S1,S2),(S3,S2),A] = ???

  def onLFrag[S1,S2,S3,A](g: Guard[S2,S3,A]): Guard[(S1,S2),(S1,S3),A] = ???

  def onFrag[S1,S2,S3,S4,A](gR: Guard[S1,S3,A],
                            gL: Guard[S2,S4,A]):
      Guard[(S1,S2), (S3,S4), A] =
    onRFrag[S1,S2,S3,A](gR) flatMap { _ => onLFrag[S3,S2,S4,A](gL) }

    (for {
       _ <- init[Unit]
       x <- unit("abc")
       y <- unit(x + "def")
     } yield y) run (()): (String, Unit)


    val db: List[(String, String, String)] = List(
      ("2014-01-01", "Bob",   "a"),
      ("2014-01-02", "Chuck", "b"),
      ("2014-01-03", "Bob",   "c"),
      ("2014-01-04", "Chuck", "d"),
      ("2014-01-05", "Bob",   "e"),
      ("2014-01-06", "Bob",   "e"),
      ("2014-01-07", "Bob",   "e"),
      ("2014-01-08", "Bob",   "f"),
      ("2014-01-08", "Daan",  "f"),
      ("2014-01-09", "Chuck", "b"),
      ("2014-01-10", "Chuck", "g"))

  println((for {
             _ <- init[db.type]
             d1 <- get[db.type]
             d2 = d1 map ({ case (d,n,a) => (d,n) })
             d3 = d2 filter({case (d,n) =>
                              List("Chuck", "Bob").exists({ _ == n }) })
           } yield d3) run (db) _1)

  def unFrag1(d1: List[(String, Int)], d2: List[(String, Int)]):
      List[(String,String,Int)] = {
    for {
      (x, i) <- d1
      (y, j) <- d2
      if i == j
    } yield (x,y,i)
  }

  println((for {
             _ <- init[db.type]
             _ <- frag1
             d1 <- get[(List[(String, Int)], List[(String, String, Int)])]
             // d2 = d1 map ({ case (d,n,a) => (d,n) })
             d21 = d1._1 map ({ case (d,i) => (d,i) })
             d22 = d1._2 map ({ case (n,a,i) => (n,i) })
             // d3 = d2 filter({case (d,n) =>
             //                  List("Chuck", "Bob").exists({ _ == n }) })
             d31 = d22 filter ({case (n,i) =>
                                 List("Chuck", "Bob").exists({ _ == n }) })
             d32 = unFrag1(d21,d31)
           } yield d32) run (db) _1)


  (for {
     _ <- init[Unit]
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
       _ <- init[Unit]
       _ <- crypt[Unit, HEq]
       x <- unit("abc")
       _ <- decrypt[HEq, Unit]
       y <- unit(x + "def")
     } yield y) run (()): (String, Unit)

    (for {
       _ <- init[Unit]
       _ <- crypt[Unit, HEq]
       _ <- crypt[HEq[Unit], HEq]
       x <- unit("abc")
       y <- unit(x + "def")
     } yield y) run (()): (String, HEq[HEq[Unit]])

    (for {
       _ <- init[Atom[Unit,Unit]]
       x <- unit("abc")
       _ <- frag
       y <- unit(x + "def")
     } yield y) run (Atom((),())): (String, (Unit, Unit))

    (for {
       _ <- init[Atom[Unit,Unit]]
       x <- unit("abc")
       _ <- frag
       y <- unit(x + "def")
     } yield y) run (Atom((),())): (String, (Unit, Unit))

    (for {
       _ <- init[Atom[Unit,Unit]]
       x <- unit("abc")
       _ <- frag
       y <- unit(x + "def")
       _ <- defrag
     } yield y) run (Atom((),())): (String, Atom[Unit,Unit])

    (for {
       _ <- init[Atom[Unit,Unit]]
       x <- unit("abc")
       _ <- frag
       _ <- onRFrag(crypt[Unit, HEq])
       z <- unit(x + "def")
       _ <- defrag
     } yield z) run (Atom((),())): (String, Atom[HEq[Unit],Unit])

    (for {
       _ <- init[Atom[Unit,Unit]]
       x <- unit("abc")
       _ <- frag
       _ <- onRFrag(for {
                      _ <- crypt[Unit, HEq]
                      _ <- crypt[HEq[Unit], HEq]
                    } yield ())
       z <- unit(x + "def")
       _ <- defrag
     } yield z) run (Atom(Unit,Unit)): (String, Atom[HEq[HEq[Unit]], Unit])

    (for {
       _ <- init[Atom[Unit,Unit]]
       x <- unit("abc")
       _ <- frag
       y <- onRFrag(for {
                      _ <- crypt[Unit, HEq]
                      _ <- crypt[HEq[Unit], HEq]
                      s <- unit("def")
                    } yield s)
       z <- unit(x + y + "ghi")
     } yield y) run (Atom(Unit,Unit)): (String, (HEq[HEq[Unit]], Unit))

    (for {
       _ <- init[Atom[Atom[Unit,Unit],Unit]]
       x <- unit("abc")
       _ <- frag
       _ <- onRFrag(for {
                      _ <- frag[Unit, Unit]
                      _ <- onRFrag(crypt[Unit, HEq])
                    } yield ())
       z <- unit(x + "def")
       _ <- defrag
     } yield z) run (Atom((Atom((),())),())): (String,
                                               Atom[(HEq[Unit],Unit), Unit])


    // type Col1 = String
    // type Col2 = String
    // type Col3 = String

    // val db: Col1 |: Col2 |: Col3 |: EOCol = DB(
    //   ("2014-01-01", "Bob",   "a"),
    //   ("2014-01-02", "Chuck", "b"),
    //   ("2014-01-03", "Bob",   "c"),
    //   ("2014-01-04", "Chuck", "d"),
    //   ("2014-01-05", "Bob",   "e"),
    //   ("2014-01-06", "Bob",   "e"),
    //   ("2014-01-07", "Bob",   "e"),
    //   ("2014-01-08", "Bob",   "f"),
    //   ("2014-01-08", "Daan",  "f"),
    //   ("2014-01-09", "Chuck", "b"),
    //   ("2014-01-10", "Chuck", "g"))

    // (for {
    //    _ <- init(db)
    //    _ <- fragDB[String |: String |: String |: EOCol](_1)
    //  } yield ())
}

object Attic {
  case class Atom[S1,S2](s1: S1, s2: S2)

  case class OldGuardian[S,+A](run: S => (A, S)) {
    def flatMap[B](f: A => OldGuardian[S,B]): OldGuardian[S,B] = OldGuardian(
      s => {
        val (a, s1) = run(s)
        f(a).run(s1)
      })

    def map[B](f: A => B): OldGuardian[S,B] =
      this flatMap(a => OldGuardian.unit(f(a)))

    def map2[B,C](sb: OldGuardian[S,B])(f: (A,B) => C): OldGuardian[S,C] =
      this flatMap(a => sb flatMap( b => OldGuardian.unit(f(a,b))))
  }

  object OldGuardian {
    type HEq[X]

    def unit[S,A](a: A): OldGuardian[S,A] = OldGuardian(s => (a, s))

    def sequence[S,A](sas: List[OldGuardian[S,A]]): OldGuardian[S,List[A]] =
      sas.foldRight(unit[S,List[A]](Nil))(
        (sa, rest) => sa.map2(rest)(_ :: _))

    // *OldGuardian combinators*

    // Combinator that modifies the state.
    def modify[S](f: S => S): OldGuardian[S, Unit] = for {
      s <- get       // Gets the current state and assigns it to `s`
      _ <- set(f(s)) // Sets the new state to `f` applied to `s`
    } yield ()

    // Combinator that gets the current state.
    def get[S]: OldGuardian[S,S] = OldGuardian((s:S) => (s, s))

    // Combinator that sets the current state.
    def set[S](s: S): OldGuardian[S, Unit] = OldGuardian(_ => ((), s))

    def crypt[P[_], S, A](g: OldGuardian[S,A]): OldGuardian[P[S], A] = ???
    def decrypt[P[_], S, A](g: OldGuardian[P[S],A]): OldGuardian[S, A] = ???

    def frag[S1,S2,A](g: OldGuardian[Atom[S1,S2],A]): OldGuardian[(S1,S2), A] = ???
    def defrag[S1,S2,A](g: OldGuardian[(S1,S2),A]): OldGuardian[Atom[S1,S2], A] = ???

    def onFrag1[S1,S2,S3,A](f: OldGuardian[S1,A] => OldGuardian[S3,A])(
                            g: OldGuardian[(S1,S2),A]): OldGuardian[(S3,S2),A] = ???

    object Tests {
      (unit[Unit, String]("abc") flatMap { s =>
       unit(s + "def") }).run(Unit)

      for {
        s <- unit[Unit, String]("abc")
        r <- unit(s + "def")
      } yield r

      unit[Unit, String]("abc") flatMap { s =>
      unit(s + "def")           flatMap { r =>
      unit(r) } }

      crypt[HEq, Unit, String](
        unit[Unit, String]("abc") flatMap { s =>
        unit(s + "def")           flatMap { r =>
        unit(r) } })

      decrypt(
        crypt[HEq, Unit, String](
          unit[Unit, String]("abc")) flatMap { s =>
        unit(s + "def")              flatMap { r =>
        unit(r) } })

      decrypt(
        decrypt(
          crypt[HEq, HEq[Unit], String](
            crypt[HEq, Unit, String](
              unit[Unit, String]("abc"))) flatMap { s =>
          unit(s + "def")                 flatMap { r =>
          unit(r) } }))

      defrag(
        frag(
          unit[Atom[Unit, Unit], String]("abc")) flatMap { s =>
        unit(s + "def")                          flatMap { r =>
        unit(r) } })

      defrag(
        onFrag1(
          crypt[HEq, Unit, String])(
          frag(
            unit[Atom[Unit, Unit], String]("abc"))) flatMap { s =>
        unit(s + "def")                             flatMap { r =>
        unit(r) } })
    }
  }
}
