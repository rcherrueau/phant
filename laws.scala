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
  def lift[T](f: T => Boolean): ((T, Id)) => Boolean = {
    case (t, id) => f(t)
  }
  def ∧[A,B](f: A => Boolean, g: B => Boolean, h: ((A,B)) => Boolean):
      ((A,B)) => Boolean = {
    case (a, b) => f(a) && g(b) && h((a,b))
  }

  // ------------------------------- γ utils
  // U ∈ P(T)
  def γ[T, U : Eq](db: DB[T])(p: T => U): DB[DB[T]] = db match {
    case Nil => Nil
    case line :: db =>
      (line :: db.filter(p(_) === p(line))) ::
        γ (db.filter(p(_) =!= p(line))) (p)
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
  def φ[T, R, E](l: DB[T])(f: T => R, g: R => E): DB[E] =
    l map (f) map (g)
  // Keeps the least identifier
  def lift[T, R](f: DB[T] => R)(implicit
                                d: DummyImplicit): DB[(T, Id)] => (R, Id) =
    tids => {
      val r = f(tids.unzip._1)
      val id = tids.minBy(_._2)._2

      (r, id)
    }
}

object Check extends App {
  import org.scalacheck.Gen
  import org.scalacheck.Arbitrary
  import org.scalacheck.Prop._
  import org.scalacheck.Test._
  import Laws._

  // A generator of tuple string int
  implicit lazy val strInt: Arbitrary[(String, Int)] = Arbitrary(for {
    str <- Gen.alphaStr
    int <- Gen.choose(1, 100)
  } yield (str, int))

  // A generator of db
  def db[A,B](gen: Gen[(A,B)]): Gen[DB[(A,B)]] = Gen.listOf(gen)

  // Property that specifies the behavior of the frag/unfrag
  // operations.
  val pIdentity =
    forAll {
      (db: DB[(String, Int)]) =>
        // unfrag\pi R1,\pi R2 ∘ frag\pi R1,\pi R2 \equiv id
        unfrag(frag(db)) == db
    }

  val pΠ =
    forAll {
      (db: DB[(String, Int)]) =>
        // \pi R ∘ unfrag\pi R1,\pi R2 \equiv id
        Π (unfrag(frag(db))) (R) == db
    } && forAll {
      (db: DB[(String, Int)]) =>
        // \pi{} R1 ∘ unfrag\pi{}R1,\pi{}R2 \equiv unfrag\pi{}R1,\pi{}R2 ∘ (\pi{} rmIdx, id)
        Π (unfrag(frag(db))) (R1) == Π (frag(db)._1) (rmId)
    } && forAll {
      (db: DB[(String, Int)]) =>
        // \pi{} R2 ∘ unfrag\pi{}R1,\pi{}R2 \equiv unfrag\pi{}R1,\pi{}R2 ∘ (id, \pi{} rmIdx)
        Π (unfrag(frag(db))) (R2) == Π (frag(db)._2) (rmId)
    }

  // σ on R for an unfragmented database is the σ on R1 for the
  // first fragment *and* the σ on R2 for the second fragement
  // *and* the σ on R for the unfragmented result of both previous
  // selection.
  // The predicate has to be in *conjonctive form*.
  val pσ =
    forAll {
      (db: DB[(String, Int)]) =>
        // \sigma _ \rightarrow true  unfrag\pi R1,\pi R2 \equiv id
        σ (unfrag(frag(db))) (_ => true) == db
    } && forAll {
      (db: DB[(String, Int)],
       f: String => Boolean,
       g: Int => Boolean,
       h: ((String, Int)) => Boolean) =>
        // \sigma (f \land g \land h) ∘ unfrag\pi R1,\pi R2 \equiv
        //   \sigma h ∘ unfrag\pi R1,\pi R2 ∘ (\sigma lift f, \sigma lift g)
        σ (unfrag(frag(db))) (∧(f, g, h)) ==
        {
          val σfrag1 = σ (frag(db)._1) (lift(f))
          val σfrag2 = σ (frag(db)._2) (lift(g))
          σ (unfrag((σfrag1, σfrag2))) (h)
        }
      } && forAll {
      (db: DB[(String, Int)],
       f: String => Boolean,
       g: Int => Boolean,
       h: ((String, Int)) => Boolean) =>
        // \sigma (f \land g \land h) ∘ unfrag\pi R1,\pi R2 \equiv
        //   \sigma h ∘ unfrag\pi R1,\pi R2 ∘ (\sigma lift f ; ids = \pi Idx,
        //                         \sigma lift g ∘ \sigma (e \rightarrow e \in ids))
        σ (unfrag(frag(db)))(∧(f, g, h)) ==
        {
          val σfrag1 = σ (frag(db)._1) (lift(f))
          val idsFrag1 = Π (σfrag1) (_._2)
          val subFrag2 = σ (frag(db)._2) {
            case (i, id) => idsFrag1.exists(_ == id)
          }
          val σfrag2 = σ (subFrag2) (lift(g))
          σ (unfrag((σfrag1, σfrag2))) (h)
        }
      } && forAll {
      (db: DB[(String, Int)],
       f: String => Boolean,
       g: Int => Boolean,
       h: ((String, Int)) => Boolean) =>
        // \sigma (f \land g \land h) ∘ unfrag\pi R1,\pi R2 \equiv
        //   \sigma h ∘ unfrag\pi R1,\pi R2 ∘ (\sigma lift f ∘ \sigma (e \rightarrow e \in ids),
        //                         \sigma lift g ; ids = \pi Idx)
        σ (unfrag(frag(db)))(∧(f, g, h)) ==
        {
          val σfrag2 = σ (frag(db)._2) (lift(g))
          val idsFrag2 = Π (σfrag2) (_._2)
          val subFrag1 = σ (frag(db)._1) {
            case (i, id) => idsFrag2.exists(_ == id)
          }
          val σfrag1 = σ (subFrag1) (lift(f))
          σ (unfrag((σfrag1, σfrag2))) (h)
        }
      } && forAll {
      (db: DB[(String, Int)],
       f: String => Boolean) =>
        // \sigma (f \land _ \rightarrow true \land _ \rightarrow true ) ∘ unfrag\pi R1,\pi R2 \equiv
        //   unfrag\pi R1,\pi R2 ∘ (\sigma lift f, id)
        σ (unfrag(frag(db))) (∧(f, _ => true, _ => true)) ==
        {
          val σfrag1 = σ (frag(db)._1) (lift(f))
          val σfrag2 = frag(db)._2
          unfrag((σfrag1, σfrag2))
        }
      } && forAll {
      (db: DB[(String, Int)],
       g: Int => Boolean) =>
        // \sigma (_ \rightarrow true \land g \land _ \rightarrow true ) ∘ unfrag\pi R1,\pi R2 \equiv
        //   unfrag\pi R1,\pi R2 ∘ (id, \sigma lift g)
        σ (unfrag(frag(db))) (∧(_ => true, g, _ => true)) ==
        {
          val σfrag1 = frag(db)._1
          val σfrag2 = σ (frag(db)._2) (lift(g))
          unfrag((σfrag1, σfrag2))
        }
      }

  // Note: What about a γ on a subpart of R1/R2? how to mix that with
  // `rmId`. For our current exemple, this in not necessary to
  // consider this.
  val pγ =
    forAll {
      (db: DB[(String, Int)]) =>
        // \gamma R1 ∘ unfrag\pi R1,\pi R2 \equiv mapunfrag1 ∘ (\gamma rmIdx, id)
        γ (unfrag(frag(db))) (R1) ==
        {
          val γfrag1 = γ (frag(db)._1) (rmId)
          val γfrag2 = frag(db)._2
          mapUnfrag1(γfrag1, γfrag2)
        }
    }  && forAll {
      (db: DB[(String, Int)]) =>
        // \gamma R2 ∘ unfrag\pi R1,\pi R2 \equiv mapunfrag2 ∘ (id, \gamma rmIdx)
        γ (unfrag(frag(db))) (R2) ==
        {
          val γfrag1 = frag(db)._1
          val γfrag2 = γ (frag(db)._2) (rmId)
          mapUnfrag2(γfrag1, γfrag2)
        }
    }

  val pφ =
    forAll {
      // φ on relation R1
      (db: DB[(String, Int)],
       f1R1: List[String] => String,
       f2R2: List[Int] => Int,
       f12R: ((String, Int)) => (String, Int)) =>
        φ (γ (unfrag(frag(db))) (R1)) (dbStrInt => {
                                         val (strs, ints) = dbStrInt.unzip
                                         (f1R1(strs), f2R2(ints))
                                       }, f12R) ==
        {
          val γfrag1 = γ (frag(db)._1) (rmId)
          val γfrag2 = frag(db)._2
          // The lift keeps the least identifier. This example makes
          // the assumption that information on left is the same for
          // all element of the group at right.
          val φfrag1 = φ (γfrag1) (lift(f1R1), identity[(String, Id)])
          val φfrag2 = φ (γfrag2) (identity, identity[(Int, Id)])
          φ (unfrag((φfrag1, φfrag2))) (identity(_), f12R)
        }
    } && forAll {
      // φ on relation R2
      (db: DB[(String, Int)],
       f1R1: List[String] => String,
       f2R2: List[Int] => Int,
       f12R: ((String, Int)) => (String, Int)) =>
        φ (γ (unfrag(frag(db))) (R2)) (dbStrInt => {
                                         val (strs, ints) = dbStrInt.unzip
                                         (f1R1(strs), f2R2(ints))
                                       }, f12R) ==
        {
          val γfrag1 = frag(db)._1
          val γfrag2 = γ (frag(db)._2) (rmId)
          val φfrag1 = φ (γfrag1) (identity, identity[(String, Id)])
          val φfrag2 = φ (γfrag2) (lift(f2R2), identity[(Int, Id)])
          φ (unfrag((φfrag1, φfrag2))) (identity(_), f12R)
        }
    }

  pIdentity.check
  pΠ.check
  pσ.check
  pγ.check
  pφ.check



  // // Bac77a
  // def zip[A]: List[A] => List[A] => List[(A, A)] =
  //   as => bs => as.zip(bs)
  // def map[A,B]: (A => B) => List[A] => List[B] =
  //   f => as =>  as.map(f)
  // def foldR[A,B]: B => ((A,B) => B) => List[A] => B =
  //   b => f => as =>  as.foldRight(b)(f)

  // import spire.syntax.ring._

  // def productImp[A](a: List[A], b: List[A])(implicit ring: Ring[A]) = {
  //   var i = 0
  //   var c = ring.zero
  //   while(i < a.size) {
  //     c = c + (a(i) * b(i))
  //       i = i + 1
  //   }
  //   c
  // }

  // // foldRight 0 + ∘ map(*) ∘ zip
  // def productFP[A](implicit ring: Ring[A]): List[A] => List[A] => A =
  //   Function.untupled({
  //     foldR[A,A](ring.zero)(_ + _) compose[List[(A,A)]]
  //       map[(A, A),A] { Function.tupled(ring.times) } compose[(List[A], List[A])]
  //       Function.tupled(Function.uncurried(zip))
  //   }).curried

  // val a = List(1,2,3,4,5)
  // val b = List(1,2,3,4,5)

  // println(productImp(a,b))
  // println(productFP[Int](implicitly)(a)(b))
}
