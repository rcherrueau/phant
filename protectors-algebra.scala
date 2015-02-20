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
    ?=(guard(flatMap_2(unit("abc")) { aes("key")(_.decode) }).get,
       guard(aes("key")("abc")).get)
  }
}
