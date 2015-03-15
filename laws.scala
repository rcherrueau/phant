import spire.algebra._, spire.implicits._

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
  // C ∈ P(T)
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

  // ------------------------------- γ utils
  // U ∈ P(T)
  def γ[T, U : Eq](db: DB[T])(p: T => U): List[List[T]] = db match {
    case Nil => Nil
    case line :: db =>
      (line :: db.filter(p(_) === p(line))) ::
        γ(db.filter(p(_) =!= p(line)))(p)
  }

  def mapUnfrag1[A, B](dbas: DB[DB[(A, Id)]],
                       dbb: DB[(B, Id)]): DB[DB[(A,B)]] =
    dbas map { dba => unfrag((dba, dbb)) }

  def mapUnfrag2[A, B](dba: DB[(A, Id)],
                       dbbs: DB[DB[(B, Id)]]): DB[DB[(A,B)]] =
    dbbs map { dbb => unfrag((dba, dbb)) }

  // ------------------------------- φ utils
  // T =:= List[(A, B)]
  // R =:= (A,B)
  def φ[T, R, E](l: List[T])(f: T => R, g: R => E): List[E] =
    l map (f) map (g)
  // Keeps the least identifier
  def φlift[T, R](f: List[T] => R): List[(T, Id)] => (R, Id) = tids => {
    val r = f(tids.unzip._1)
    val id = tids.minBy(_._2)._2

    (r, id)
  }
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

  val pΠ =
    forAll (db(strInt)) {
      // Π on relation R
      db => Π (unfrag(frag(db))) (R) == db
    } && forAll (db(strInt)) {
      // Π on relation R1
      db => Π (unfrag(frag(db))) (R1) == Π (frag(db)._1) (rmId)
    } && forAll (db(strInt)) {
      // Π on relation R2
      db => Π (unfrag(frag(db))) (R2) == Π (frag(db)._2) (rmId)
    }

  val p1R1: String => Boolean = _.startsWith("a")
  val p2R2: Int => Boolean = _ % 2 == 0
  val p12R: ((String, Int)) => Boolean = _ => true
  val pσ =
    forAll (db(strInt)) {
      // σ on relation R: predicate is in conjonctive form
      db => σ (unfrag(frag(db)))(∧(p1R1, p2R2, p12R)) == {
        val σfrag1 = σ (frag(db)._1) (σlift(p1R1))
        val σfrag2 = σ (frag(db)._2) (σlift(p2R2))
        σ(unfrag((σfrag1, σfrag2))) (p12R)
      }
    } && forAll(db(strInt)) {
      // σ on relation R1: predicate is in conjonctive form
      db => σ (unfrag(frag(db))) (∧(p1R1, _ => true, _ => true)) == {
        val σfrag1 = σ (frag(db)._1) (σlift(p1R1))
        val σfrag2 = frag(db)._2
        unfrag((σfrag1, σfrag2))
      }
    } && forAll(db(strInt)) {
      // σ on relation R2: predicate is in conjonctive form
      db => σ (unfrag(frag(db))) (∧(_ => true, p2R2, _ => true)) == {
        val σfrag1 = frag(db)._1
        val σfrag2 = σ (frag(db)._2) (σlift(p2R2))
        unfrag((σfrag1, σfrag2))
      }
    }

  val pγ =
    /*forAll (db(strInt)) {
      // γ on relation R seems not fragmentable
      db => γ (unfrag(frag(db))) (R) == {
        val γfrag1: DB[DB[(String, Id)]]= γ (frag(db)._1) (R1)
        val γfrag2: DB[DB[(Int, Id)]] = γ (frag(db)._2) (R2)

      }
    } &&*/ forAll (db(strInt)) {
      // γ on relation R1
      db => γ (unfrag(frag(db))) (R1) == {
        val γfrag1 = γ (frag(db)._1) (R1)
        val γfrag2 = frag(db)._2
        mapUnfrag1(γfrag1, γfrag2)
      }
    } && forAll (db(strInt)) {
      // γ on relation R2
      db => γ (unfrag(frag(db))) (R2) == {
        val γfrag1 = frag(db)._1
        val γfrag2 = γ (frag(db)._2) (R2)
        mapUnfrag2(γfrag1, γfrag2)
      }
    }

  val f1R1: List[String] => String = _.head
  val f2R2: List[Int] => Int = _.head
  val f12R: ((String, Int)) => (String, Int) = identity
  val pφ =
    forAll (db(strInt)) {
      // φ on relation R1
      db => φ (γ (unfrag(frag(db))) (R1)) (dbStrInt => {
                                             val (strs, ints) = dbStrInt.unzip
                                             (f1R1(strs), f2R2(ints))
                                           }, f12R) == {
        val γfrag1 = γ (frag(db)._1) (R1)
        val γfrag2 = frag(db)._2
        val φfrag1 = φ (γfrag1) (φlift(f1R1), identity[(String, Id)])
        val φfrag2 = φ (γfrag2) (identity, identity[(Int, Id)])
        φ (unfrag((φfrag1, φfrag2))) (identity(_), f12R)
      }
    } && forAll (db(strInt)) {
      // φ on relation R2
      db => φ (γ (unfrag(frag(db))) (R2)) (dbStrInt => {
                                             val (strs, ints) = dbStrInt.unzip
                                             (f1R1(strs), f2R2(ints))
                                           }, f12R) == {
        val γfrag1 = frag(db)._1
        val γfrag2 = γ (frag(db)._2) (R2)
        val φfrag1 = φ (γfrag1) (identity, identity[(String, Id)])
        val φfrag2 = φ (γfrag2) (φlift(f2R2), identity[(Int, Id)])
        φ (unfrag((φfrag1, φfrag2))) (identity(_), f12R)
      }
    }

}
