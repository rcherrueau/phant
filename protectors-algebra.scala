package phant

import scala.language.higherKinds
import spire.algebra._
import spire.implicits._

/*
monad Guardian[P[R],A]
 return: A => Guardian[P[R],A]
 bind: Guardian[P[R]A] => (A => Guardian[P[R],B]) => Guardian[P[R],B]
 crypt: P => R => Guardian[P[R],_] // put
 decrypt: P => Guardian[P[R],R] // get
 modify: (R => R) => Guardian[P[R],_]

String => List[(A, String)]
List[String => (A, String)]

Guardian[P1[R],A] => Guardian[P2[R],A] => Guardian[P2[P1[R]],A]

frag: Int => DB => Guardian[Frag[(DB.frag1, DB.frag2)],A]
join:

Guardian[Frag[(DB.frag1, DB.frag2)],A]

// 1. Fragment,
// 2. chiffre AES (Symmetric) cols 1er frag
// 3. pull cols 2em frag chez owner.

frag1: Guardian[DB.frag1,A] => Guardian[Frag[(DB.frag1, DB.frag2)],A]

// 2 choix:
// 1. L'état représente l'évolution de la structure de la rsc.
// => Pile monadic ? Lift
// 2. Calcul monadic: le calcul représente l'évolution de la
//    structure de la rsc.
// =>

// Split state in two parts:
frag: Guardian[P[(R1,R2)], Unit] => Guardian[(P[R1],P[R2]), Unit]
frag: Guardian[C[R1 F: R2], Unit] => Guardian[C[R1] F: C[R2], Unit]

join: Guardian[(P[R1],P[R2]), Unit] => Guardian[P[(R1,R2)], Unit]

// Does some calculi on first frag
onFrag1: Guardian[P[R1], Unit] => Guardian[(P[R1],P[R2]), Unit]
*/

case class Guardian[S1,S2,+A](run: S1 => (A, S2)) {
  def flatMap[B,S3](f: A => Guardian[S2,S3,B]): Guardian[S1,S3,B] = Guardian(
    (s1: S1) => {
      val (a, s2) = this.run(s1)
      f(a).run(s2)
    })

  def map[B](f: A => B): Guardian[S1,S2,B] =
     this flatMap { a => Guardian.unit(f(a)) }
}

object Guardian {
  case class Atom[S1,S2](s1: S1, s2: S2) // State is splitable onto S1, S2
  type HEq[R]

  def unit[S,A](a: A): Guardian[S,S,A] = Guardian(s => (a, s))

  def crypt[S,P[_]]: Guardian[S,P[S],Unit] = ???
  def cryptHEq[S]: Guardian[S,HEq[S],Unit] = ???

  def decrypt[P[_], S]: Guardian[P[S], S, Unit] = ???

  // TODO: Dependent type on Atom
  // trait Atom[S] {type S1 type S2}
  // object Atom {
  //   implicit object UAtom extends Atom[Unit] { type S1 = Unit ; type S2 = Unit }
  // }
  // def frag[S](implicit atom: Atom[S]): Guardian[S, (atom.S1, atom.S2), Unit] = ???
  // unit("abc") flatMap { x => frag }: Guardian[Unit, (Unit, Unit), Unit]
  def frag[S1,S2]: Guardian[Atom[S1,S2], (S1,S2), Unit] = ???

  def defrag[S1,S2]: Guardian[(S1,S2), Atom[S1,S2], Unit] = ???

  def onFrag1[S1,S2,S3,A](g: Guardian[S1,S3,A]): Guardian[(S1,S2),(S3,S2),A] = ???

  object Test {
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
        unit("def") map     { d => s + d }: Guardian[HEq[Unit], HEq[Unit], String]
      }: Guardian[Unit, HEq[Unit], String]
    }: Guardian[Unit, HEq[Unit], String]

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
       _ <- onFrag1(crypt[Unit, HEq])
       z <- unit(x + "def")
       _ <- defrag
     } yield z) run (Atom((),())): (String, Atom[HEq[Unit],Unit])

    (for {
       x <- unit("abc")
       _ <- frag[Unit, Unit]
       _ <- onFrag1(for {
                      _ <- crypt[Unit, HEq]
                      _ <- crypt[HEq[Unit], HEq]
                    } yield ())
       z <- unit(x + "def")
       _ <- defrag
     } yield z) run (Atom(Unit,Unit)): (String, Atom[HEq[HEq[Unit]], Unit])

    (for {
       x <- unit("abc")
       _ <- frag[Unit, Unit]
       _ <- onFrag1(for {
                      _ <- crypt[Unit, HEq]
                      _ <- crypt[HEq[Unit], HEq]
                    } yield ())
       z <- unit(x + "def")
       _ <- defrag
     } yield z) run (Atom(Unit,Unit)): (String, Atom[HEq[HEq[Unit]], Unit])

    (for {
       x <- unit("abc")
       _ <- frag[Unit, Unit]
       y <- onFrag1(for {
                      _ <- crypt[Unit, HEq]
                      _ <- crypt[HEq[Unit], HEq]
                      s <- unit("def")
                    } yield s)
       z <- unit(x + y + "ghi")
     } yield y) run (Atom(Unit,Unit)): (String, (HEq[HEq[Unit]], Unit))

    (for {
       x <- unit("abc")
       _ <- frag[Atom[Unit,Unit], Unit]
       _ <- onFrag1(for {
                      _ <- frag[Unit, Unit]
                      _ <- onFrag1(crypt[Unit, HEq])
                    } yield ())
       z <- unit(x + "def")
       _ <- defrag
     } yield z) run (Atom((Atom((),())),())): (String,
                                               Atom[(HEq[Unit],Unit), Unit])
  }
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
