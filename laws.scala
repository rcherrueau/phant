import shapeless._

// trait Laws {
//   type Id = Int
//   val db: List[(String, Unit)]
//   val frag1: List[(String, Id)]
//   val frag2: List[(Unit, Id)]
//   val gdb: List[List[(String, Unit)]]
//   val gfrag1: List[List[(String, Id)]]
//   val gfrag2: List[List[(Unit, Id)]]

//   //---------------------------------------------------------------- Id
//   def frag[A,B](l: List[(A,B)]): (List[(A,Id)], List[(B, Id)])
//   def unfrag[A,B](f: (List[(A,Id)], List[(B, Id)])): List[(A,B)]

//   // -- identity
//   unfrag(frag(db)):                            List[(String, Unit)] // =
//   identity(db):                                List[(String, Unit)]
//   // --

//   def Π1[A,B]:((A,B)) => A
//   def Π2[A,B]:((A,B)) => B
//   def rmId[A]:((A, Id)) => A

//   //------------------------------------------------------------ Project
//   def project[T,C](l: List[T])(f: T => C): List[C]

//   // -- project on 1
//   project(unfrag(frag(db)))(Π1):               List[String] // =
//   project(frag(db)._1)(rmId):                  List[String]
//   // --

//   // -- project on 2
//   project(unfrag(frag(db)))(Π2):               List[Unit] // =
//   project(frag(db)._2)(rmId):                  List[Unit]
//   // --

//   //------------------------------------------------------------ Select
//   def select[T](l: List[T])(f1: T => Boolean): List[T]
//   def slift[T](f: T => Boolean): ((T, Id)) => Boolean
//   val p1: String => Boolean
//   val p2: Unit => Boolean
//   val p12: ((String, Unit)) => Boolean

//   // -- select p1 @ Π1, p2 @ Π2, p12 @ Π12
//   {
//     select(unfrag(frag(db))) {
//       case (s,u) => p1(s) && p2(u) && p12((s,u))
//     }:                                         List[(String, Unit)] // =

//     // Two possibilities: 1) Use rmId, 2) Lift p*@Π*
//     val ff1 = select(frag1) (slift(p1))
//     val ff2 = select(frag2) (slift(p2))
//     select(unfrag((ff1, ff2))) (p12):          List[(String, Unit)]
//   }
//   // --

//   // -- select p1 @ Π1
//   {
//     select(unfrag(frag(db))) {
//       case (s,u) => p1(s)
//     }:                                         List[(String, Unit)] // =

//     val ff1 = select(frag1) (slift(p1))
//     val ff2 = identity(frag2)
//     unfrag((ff1, ff2)):                        List[(String, Unit)]
//   }
//   // --


//   //------------------------------------------------------------ GroupBy
//   def groupby[T,U](l: List[T])(f: T => U): List[List[T]]
//   def mapUnfrag1[A,B](gl: List[List[(A, Id)]],
//                       lb: List[(B, Id)]): List[List[(A,B)]] =
//     gl map { la => unfrag(la, lb) }

//   // -- groupby Π1
//   {
//     groupby(unfrag(frag(db)))(Π1):             List[List[(String, Unit)]] // =

//     val gf1 = groupby(frag1)(Π1)
//     val gf2 = identity(frag2)
//     mapUnfrag1(gf1, gf2):                      List[List[(String, Unit)]]
//   }
//   // --


//   //--------------------------------------------------------------- Fold
//   def fold[T,R,E](l: List[T])(f: T => R, g: R => E): List[E]
//   def flift[T,R](f: List[T] => R): List[(T, Id)] => (R, Id)
//   val f1: List[String] => String
//   val f2: List[Unit] => Unit
//   val f12: ((String, Unit)) => (String, Int)


//   {
//     fold(gdb) (lab => {
//                  val (la, lb) = lab.unzip
//                    (f1(la), f2(lb))
//                }, f12):                        List[(String, Int)] // =

//     val ff1 = fold(gfrag1) (flift(f1), identity[(String, Id)])
//     val ff2 = fold(gfrag2) (flift(f2), identity[(Unit, Id)])
//     fold(unfrag((ff1, ff2))) (identity(_), f12)
//   }
// }

object Laws {
  type DB[A] = List[A]
  type Id = Int

  def frag[A, B](db: DB[(A, B)]): (DB[(A, Id)], DB[(B, Id)]) = {
    val (split1, split2) = db.unzip
    (split1.zipWithIndex, split2.zipWithIndex)
  }

  // Join with intersection
  def unfrag[A, B](frags: (DB[(A, Id)], DB[(B, Id)])): DB[(A, B)] = {
    val (frag1, frag2) = frags
    for {
      (a, i) <- frag1
      (b, j) <- frag2
      if (i == j)
    } yield (a, b)
  }

  // ------------------------------- Π utils
  // C should be a subset of T
  def Π[T, C](db: DB[T])(p: T => C): DB[C] = db.map(p)

  def R[A, B]: ((A, B)) => ((A,B)) = identity
  def R1[A, B]: ((A, B)) => A = _._1
  def R2[A, B]: ((A, B)) => B = _._2
  def rmId[A]: ((A, Id)) => A = _._1

  // -------------------------------- σ utils
  def σ[T](db: DB[T])(p: T => Boolean): DB[T] = db.filter(p)
  def σlift[T](f: T => Boolean): ((T, Id)) => Boolean = {
    case (t, id) => f(t)
  }
  def ∧[A,B](f: A => Boolean, g: B => Boolean, h: ((A,B)) => Boolean):
      ((A,B)) => Boolean = {
    case (a, b) => f(a) && g(b) && h((a,b))
  }

// def flift[T, R](f: DB[T] => R): DB[(T, Id)] => (R, Id) = ???
// def fold[T, R, E](l: DB[T])(f: T => R,g: R => E): DB[E] = ???
// val frag1: DB[(String, Id)] = ???
// val frag2: DB[(Unit, Id)] = ???
// val gdb: DB[DB[(String, Unit)]] = ???
// val gfrag1: DB[DB[(String, Id)]] = ???
// val gfrag2: DB[DB[(Unit, Id)]] = ???
// def groupby[T, U](l: DB[T])(f: T => U): DB[DB[T]] = ???
// val p1: String => Boolean = ???
// val p12: ((String, Unit)) => Boolean = ???
// val p2: Unit => Boolean = ???
// def select[T](l: DB[T])(f1: T => Boolean): DB[T] = ???

}

object Check {
  import org.scalacheck.Gen
  import org.scalacheck.Prop._
  import Laws._

  // A generator of tuple string int
  val strInt: Gen[(String, Int)] = for {
    str <- Gen.alphaStr
    int <- Gen.choose(1, 100)
  } yield (str, int)

  // A generator of db
  def db[A,B](gen: Gen[(A,B)]): Gen[DB[(A,B)]] = Gen.listOf(gen)

  // A property that specifies the behavior of the frag/unfag method
  val fragUnfrag =
    forAll (db(strInt)) {
      db => unfrag(frag(db)) == db
    }

  val project =
    forAll (db(strInt)) {
      db => Π (unfrag(frag(db))) (R1) == Π (frag(db)._1) (rmId)
    } && forAll (db(strInt)) {
      db => Π (unfrag(frag(db))) (R2) == Π (frag(db)._2) (rmId)
    }

  val p1R1: String => Boolean = _.startsWith("a")
  val p2R2: Int => Boolean = _ % 2 == 0
  val p12R: ((String, Int)) => Boolean = _ => true
  val select =
    forAll (db(strInt)) {
      // Conjonctive form is threadable
      db => σ (unfrag(frag(db)))(∧(p1R1, p2R2, p12R)) == {
        val σfrag1 = σ (frag(db)._1) (σlift(p1R1))
        val σfrag2 = σ (frag(db)._2) (σlift(p2R2))
        σ(unfrag((σfrag1, σfrag2))) (p12R)
      }
    } && forAll(db(strInt)) {
      db => σ (unfrag(frag(db))) (∧(p1R1, _ => true, _ => true)) == {
        val σfrag1 = σ (frag(db)._1) (σlift(p1R1))
        val σfrag2 = frag(db)._2
        unfrag((σfrag1, σfrag2))
      }
    } && forAll(db(strInt)) {
      db => σ (unfrag(frag(db))) (∧(_ => true, p2R2, _ => true)) == {
        val σfrag1 = frag(db)._1
        val σfrag2 = σ (frag(db)._2) (σlift(p2R2))
        unfrag((σfrag1, σfrag2))
      }
    }

}
