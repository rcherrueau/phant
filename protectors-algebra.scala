package phant

import scala.language.higherKinds
import fpinscala._
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


// P[R] is my state in state monad


case class Guardian[S,+A](run: S => (A, S)) {
  def flatMap[B](f: A => Guardian[S,B]): Guardian[S,B] = Guardian(
    s => {
      val (a, s1) = run(s)
      f(a).run(s1)
    })

  def map[B](f: A => B): Guardian[S,B] =
    this flatMap(a => Guardian.unit(f(a)))

  def map2[B,C](sb: Guardian[S,B])(f: (A,B) => C): Guardian[S,C] =
    this flatMap(a => sb flatMap( b => Guardian.unit(f(a,b))))
}

case class Atom[A,B](s1: A, s2: B) {
  type S1 = A
  type S2 = B
}

object Guardian {
  def unit[S,A](a: A): Guardian[S,A] = Guardian(s => (a, s))

  def sequence[S,A](sas: List[Guardian[S,A]]): Guardian[S,List[A]] =
    sas.foldRight(unit[S,List[A]](Nil))(
      (sa, rest) => sa.map2(rest)(_ :: _))

  // *Guardian combinators*

  // Combinator that modifies the state.
  def modify[S](f: S => S): Guardian[S, Unit] = for {
    s <- get       // Gets the current state and assigns it to `s`
    _ <- set(f(s)) // Sets the new state to `f` applied to `s`
  } yield ()

  // Combinator that gets the current state.
  def get[S]: Guardian[S,S] = Guardian((s:S) => (s, s))

  // Combinator that sets the current state.
  def set[S](s: S): Guardian[S, Unit] = Guardian(_ => ((), s))

  def crypt[P[_], S, A](g: Guardian[S,A]): Guardian[P[S], A] = ???
  def decrypt[P[_], S, A](g: Guardian[P[S],A]): Guardian[S, A] = ???

  // frag: Guardian[P[(R1,R2)], Unit] => Guardian[(P[R1],P[R2]), Unit]
  // frag: Guardian[C[R1 F: R2], Unit] => Guardian[C[R1] F: C[R2], Unit]
  def frag[S1,S2,A](g: Guardian[Atom[S1,S2],A]): Guardian[(S1,S2), A] = ???
  def defrag[S1,S2,A](g: Guardian[(S1,S2),A]): Guardian[Atom[S1,S2], A] = ???

  def onFrag1[S1,S2,S3,A](f: Guardian[S1,A] => Guardian[S3,A])(
                          g: Guardian[(S1,S2),A]): Guardian[(S3,S2),A] = ???
}


case class Guardian2[S1,S2,+A](run: S1 => (A, S2)) {
  def flatMap[B,S3](f: A => Guardian2[S2,S3,B]): Guardian2[S1,S3,B] = Guardian2(
    (s1: S1) => {
      val (a, s2) = this.run(s1)
      f(a).run(s2)
    })

  def map[B](f: A => B): Guardian2[S1,S2,B] =
     this flatMap { a => Guardian2.unit(f(a)) }
}

object Guardian2 {
  trait Protection { def get: String }
  trait Raw[R] extends Protection { def decode: R }
  type Pull[C] <: Protection
  type AES[R] <: Protection
  type HES <: Protection
  type HEq[R] <: HES
  type HOrder[R] <: HEq[R]

  def unit[S,A](a: A): Guardian2[S,S,A] = Guardian2(s => (a, s))

  def crypt[P[_],S]: Guardian2[S,P[S],Unit] = ???
  def cryptHEq[S]: Guardian2[S,HEq[S],Unit] = ???

  def decrypt[P[_], S]: Guardian2[P[S], S, Unit] = ???

  // // frag: Guardian2[P[(R1,R2)], Unit] => Guardian2[(P[R1],P[R2]), Unit]
  // // frag: Guardian2[C[R1 F: R2], Unit] => Guardian2[C[R1] F: C[R2], Unit]
  // def frag[S1,S2,A](g: Guardian2[Atom[S1,S2],A]): Guardian2[(S1,S2), A] = ???
  // TODO: Dependent type on Atom
  def frag[S1, S2]: Guardian2[Atom[S1,S2], (S1,S2), Unit] = ???

  // def defrag[S1,S2,A](g: Guardian2[(S1,S2),A]): Guardian2[Atom[S1,S2], A] = ???
  def defrag[S1,S2]: Guardian2[(S1,S2), Atom[S1,S2], Unit] = ???

  // def onFrag1[S1,S2,S3,A](f: Guardian2[S1,A] => Guardian2[S3,A])(
  //                         g: Guardian2[(S1,S2),A]): Guardian2[(S3,S2),A] = ???
  def onFrag1[S1,S2,S3,A](g: Guardian2[S1,S3,A]): Guardian2[(S1,S2),(S3,S2),A] = ???
}


object Test {
  import Guardian2.HEq

  (Guardian.unit[Unit, String]("abc") flatMap { s => Guardian.unit(s + "def") }).run(Unit)

  for {
    s <- Guardian.unit[Unit, String]("abc")
    r <- Guardian.unit(s + "def")
  } yield r


  /*
   Guardian.unit[Unit, String]("abc") bind { s =>
   Guardian.unit(s + "def")           bind { r =>
   Guardian.unit(r) } }
   */

  val a =
  Guardian.unit[Unit, String]("abc") flatMap { s =>
  Guardian.unit(s + "def")           flatMap { r =>
  Guardian.unit(r) } }

  val b =
  Guardian.crypt[HEq, Unit, String](
    Guardian.unit[Unit, String]("abc") flatMap { s =>
    Guardian.unit(s + "def")           flatMap { r =>
    Guardian.unit(r) } }
    )

  val c: Guardian[Unit,String] =
  Guardian.decrypt(
    Guardian.crypt[HEq, Unit, String](
      Guardian.unit[Unit, String]("abc")) flatMap { s =>
    Guardian.unit(s + "def")              flatMap { r =>
    Guardian.unit(r) } })
  c.run(Unit)

  val d: Guardian[Unit,String] =
  Guardian.decrypt(
    Guardian.decrypt(
      Guardian.crypt[HEq, HEq[Unit], String](
        Guardian.crypt[HEq, Unit, String](
          Guardian.unit[Unit, String]("abc"))) flatMap { s =>
      Guardian.unit(s + "def")                 flatMap { r =>
      Guardian.unit(r) } }))
  d.run(Unit)

  val e: Guardian[Atom[Unit, Unit], String] =
  Guardian.defrag(
    Guardian.frag(
      Guardian.unit[Atom[Unit, Unit], String]("abc")) flatMap { s =>
    Guardian.unit(s + "def")                          flatMap { r =>
    Guardian.unit(r) } })
  e.run(Atom(Unit,Unit))

  val f: Guardian[Atom[HEq[Unit], Unit], String] =
  Guardian.defrag(
    Guardian.onFrag1(
      Guardian.crypt[HEq, Unit, String])(
      Guardian.frag(
        Guardian.unit[Atom[Unit, Unit], String]("abc"))) flatMap { s =>
    Guardian.unit(s + "def")                             flatMap { r =>
    Guardian.unit(r) } })
  // f.run(Atom(Unit,Unit))


  for {
    s <- Guardian2.unit[Unit, String]("abc")
    r <- Guardian2.unit(s + "def")
  } yield r

  for {
    _ <- Guardian2.crypt[HEq, Unit]
    s <- Guardian2.unit[HEq[Unit], String]("abc")
    _ <- Guardian2.decrypt[HEq, Unit]
    r <- Guardian2.unit(s + "def")
  } yield r

  (for {
    _ <- Guardian2.crypt[HEq, Unit]
    s <- Guardian2.unit("abc")
    r <- Guardian2.unit(s + "def")
   } yield r).run(Unit)

  (for {
    _ <- Guardian2.crypt[HEq, Unit]
    _ <- Guardian2.crypt[HEq, HEq[Unit]]
    s <- Guardian2.unit("abc")
    r <- Guardian2.unit(s + "def")
   } yield r).run(Unit)

  (for {
    _ <- Guardian2.frag[Unit, Unit]
    s <- Guardian2.unit("abc")
    r <- Guardian2.unit(s + "def")
   } yield r).run(Atom(Unit,Unit))

  (for {
     s <- Guardian2.unit("abc")
     _ <- Guardian2.frag[Unit, Unit]
     r <- Guardian2.unit(s + "def")
   } yield r).run(Atom(Unit,Unit))

  (for {
     s <- Guardian2.unit("abc")
     _ <- Guardian2.frag[Unit, Unit]
     r <- Guardian2.unit(s + "def")
     _ <- Guardian2.defrag
   } yield r).run(Atom(Unit,Unit))

  (for {
     s <- Guardian2.unit("abc")
     _ <- Guardian2.frag[Unit, Unit]
     v <- Guardian2.onFrag1(Guardian2.crypt[HEq, Unit])
     r <- Guardian2.unit(s + "def")
     _ <- Guardian2.defrag
   } yield r).run(Atom(Unit,Unit))

  (for {
     s <- Guardian2.unit("abc")
     _ <- Guardian2.frag[Unit, Unit]
     v <- Guardian2.onFrag1(for {
                              _ <- Guardian2.crypt[HEq, Unit]
                              _ <- Guardian2.crypt[HEq, HEq[Unit]]
                            } yield ())
     r <- Guardian2.unit(s + "def")
     _ <- Guardian2.defrag
   } yield r).run(Atom(Unit,Unit))

  (for {
     s <- Guardian2.unit("abc")
     _ <- Guardian2.frag[Unit, Unit]
     v <- Guardian2.onFrag1(for {
                              _ <- Guardian2.cryptHEq[Unit]
                              _ <- Guardian2.cryptHEq[HEq[Unit]]
                            } yield ())
     r <- Guardian2.unit(s + "def")
     _ <- Guardian2.defrag
   } yield r).run(Atom(Unit,Unit))
}


// case


// trait Al[P[_], R] {
//   type Guardian[P, +A] <: State[P,A]

//   def unit[A](a: A): Guardian[P[R],A]

//   def flatMap[A,B](g: Guardian[P[R],A])(
//                    f: A => Guardian[P[R],B]): Guardian[P[R],B]

//   def map[A,B](g: Guardian[P[R],A])(
//                f: A => B): Guardian[P[R],B]

//   object Test {
//     import Guardian._

//     // val a: Guardian[AES[String], Unit] =
//     //   Guardian.crypt(aes("key")("abc"))

//     // val b: Guardian[HEq[String], Unit] =
//     //   Guardian.crypt(heq("pkey")("abc"))
//     // b.run(heq("pkey")("abc"))

//     // val c: Guardian[HEq[String], Unit] =
//     //   Guardian.crypt[HEq,String]
//     // c.run(heq("pkey")("abc"))

//     val d: Guardian[HEq[String], Unit] = Guardian.crypt[HEq](unit("abc"))




//   }

//   object Guardian {
//     def crypt[P[_]](g: Guardian[R, Unit]): Guardian[P[R], Unit] = ???
//     // P => Guardian[R, Unit] => Guardian[P[R], Unit]


//     def crypt[P[_],R](pr: P[R]): Guardian[P[R], Unit] = ???

//     def decrypt[P[_],R]: Guardian[P[R],R] = ???


//     trait Protection { def get: String }
//     trait Raw[R] extends Protection { def decode: R }
//     type Pull[C] <: Protection
//     type AES[R] <: Protection
//     type HES <: Protection
//     type HEq[R] <: HES
//     type HOrder[R] <: HEq[R]

//     def aes[R](k: String)(r: R): AES[R] = ???
//     def heq[R: Eq](pk: String)(r: R): HEq[R] = ???
//     def horder[R: Order](pk: String)(r: R): HOrder[R] = ???
//     def pull[C](c: => C): Pull[C] = ???
//   }

// }


// Guardian embed a protection. It protects a resource.
trait Algebra[Guardian[P[_],R]] {
  // Protection has a representaion of resource in String
  trait Protection { def get: String }
  trait Raw[R] extends Protection { def decode: R }
  type Pull[C] <: Protection
  type AES[R] <: Protection
  type HES <: Protection
  type HEq[R] <: HES
  type HOrder[R] <: HEq[R]
  // type HAdd[R] <: HES
  // type HMul[R] <: HES

  type R[A] = State[Int,A]

  /** No protection. */
  def unit[R](r: R): Guardian[Raw,R]

  /** Guard with AES encryption. */
  def aes[R](k: String)(r: R): Guardian[AES,R]

  /** Guard with HEq encryption.
    *
    * See CryptDB algorithm, EQ
    * http://css.csail.mit.edu/cryptdb
    */
  def heq[R: Eq](pk: String)(r: R): Guardian[HEq,R]

  /** Guard with HOrder encryption.
    *
    * See CryptDB algorithm, OPE
    * http://css.csail.mit.edu/cryptdb
    */
  def horder[R: Order](pk: String)(r: R): Guardian[HOrder,R]

  /** Guard with computation/resource pulling */
  def pull[C](c: => C): Guardian[Pull,C]

  // /** Guard with resource encryption (HAdd) */
  // def hadd[R: AdditiveMonoid](pk: String)(r: R): Guardian[HAdd,R]

  // /** Guard with resource encryption (HMul) */
  // def hmul[R: MultiplicativeMonoid](pk: String)(r: R): Guardian[HMul,R]

  // // TODO:
  // // Question ? Est-ce frag peux être minimale, eg: just décoouper
  // // avec index. Et du coup j'utilise mes combinateurs pour faire des
  // // truc interesssant.
  // // Idea: Typeclass for splitable data.
  // /** Protects with fragmentation */
  // // def frag

  // Two implementations possible:
  // - First one accesses to resources. Not sure this is possible with
  //   polymorphisme
  def flatMap[P1[_], P2[_], R](p: Guardian[P1,R])(
                               f: R => Guardian[P2,R]): Guardian[P2,R]
  // - Second one accesses to protection.
  def flatMap_2[P1[_], P2[_], R](p: Guardian[P1,R])(
                                 f: P1[R] => Guardian[P2,R]): Guardian[P2,R]

  def map[P1[_],R,P2[_]](p: Guardian[P1,R])(
                         f: P1[R] => P2[R]): Guardian[P2,R]

  /** Running a guardian */
  trait Result[P[_],R] {
    // Returns a string representation of the result.
    def get: String
  }
  def guard[P[_],R](p: Guardian[P,R]): Result[P,R]

  object Laws {
    import scala.language.postfixOps
    import org.scalacheck.Gen
    import org.scalacheck.Prop._
    import org.scalacheck.Prop

    ?=(guard(unit("abc")).get, "abc") &&
    // Base64 representation
    ?=(guard(aes("key")("abc")).get, "557FUEP2/VtcJ10n7wYCZA==") &&
    ?=(guard(heq("pkey")("abc")).get, "557FUEP2/VtcJ10n7wYCZA==") &&
    ?=(guard(horder("pkey")("abc")).get, "557FUEP2/VtcJ10n7wYCZA==") &&
    // Predicatble uniq id
    ?=(guard(pull(println("abc"))).get, "e56e9e25-3cac-4a1b-8449") &&
    // Here, the guardian is in charge of extracting "abc"
    ?=(guard(flatMap(unit("abc")) { aes("key")(_) }).get,
       guard(aes("key")("abc")).get) &&
    // Here I have to deal with Raw to extract "abc"
    ?=(guard(flatMap_2(unit("abc")) { s => aes("key")(s.decode) }).get,
       guard(aes("key")("abc")).get)
  }
}
