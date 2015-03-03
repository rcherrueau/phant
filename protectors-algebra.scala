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

  // def frag1: Guard[List[(String,String,String)],
  //                  (List[(String,Int)],
  //                   List[(String,String,Int)]),
  //                  Unit] = Guard(db =>
  //                    ((), (db.zipWithIndex.map {
  //                                case ((d,_,_), v) => (d, v)
  //                              },
  //                              db.zipWithIndex.map {
  //                                case ((_,n,a), v) => (n, a, v)
  //                              })))


  def defrag[S1,S2]: Guard[(S1,S2), Atom[S1,S2], Unit] =
    Guard({ case (s1, s2) => ((), Atom(s1, s2)) })

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


  (for {
     _ <- init[db.type]
     d1 <- get[db.type]
     d2 = d1 map ({ case (d,n,a) => (d,n) })
     d3 = d2 filter({case (d,n) =>
                      List("Chuck", "Bob").exists({ _ == n }) })
   } yield d3)


  def unFrag1(d1: List[(String, Int)], d2: List[(String, Int)]):
      List[(String,String,Int)] = {
    for {
      (x, i) <- d1
      (y, j) <- d2
      if i == j
    } yield (x,y,i)
  }

  // (for {
  //    _ <- init[db.type]
  //    _ <- frag1
  //    d1 <- get[(List[(String, Int)], List[(String, String, Int)])]
  //    // d2 = d1 map ({ case (d,n,a) => (d,n) })
  //    d21 = d1._1 map ({ case (d,i) => (d,i) })
  //    d22 = d1._2 map ({ case (n,a,i) => (n,i) })
  //    // d3 = d2 filter({case (d,n) =>
  //    //                  List("Chuck", "Bob").exists({ _ == n }) })
  //    d31 = d22 filter ({case (n,i) =>
  //                        List("Chuck", "Bob").exists({ _ == n }) })
  //    d32 = unFrag1(d21,d31)
  //  } yield d32)


  trait Site[A, S[X]] {
    def get: A
    def apply[B](b: B): S[B]
    def move[S[A] <: Site[A,S]](f: A => S[A]): S[A] = f(get)
    // // def project[Z <: A,Y](f: Z => Y): Site[List[Y]] = ???
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

  object Site {
    def s0[A](a: A) = Site0(a)
    def s1[A](a: A) = Site1(a)
    def s2[A](a: A) = Site2(a)

    def map[Y,Z,S[X] <: Site[X,S]](s: S[List[Y]])(f: Y => Z): S[List[Z]] =
      s(s.get map f)

    def filter[Y,S[X] <: Site[X,S]](s: S[List[Y]])(f: Y => Boolean): S[List[Y]] =
      s(s.get filter f)

    def join[S[X] <: Site[X,S]](s1: S[List[(String,Int)]],
                                s2: S[List[(String,Int)]]):
        S[List[(String,String,Int)]] =
      s1(for {
           (x, i) <- s1.get
           (y, j) <- s2.get
           if i == j
         } yield (x, y, i))
  }

  import Site._

  def frag1:Guard[Site0[List[(String,String,String)]],
                   (Site1[List[(String,Int)]],
                    Site2[List[(String,String,Int)]]),
                   Unit] =
    Guard(db =>
      ((), (Site1(db.get.zipWithIndex.map {
                    case ((d,_,_), v) => (d, v)
                  }),
            Site2(db.get.zipWithIndex.map {
                    case ((_,n,a), v) => (n, a, v)
                  }))))

  (for {
     _ <- init[Site0[List[(String,String,String)]]]
     _ <- frag1
     d1 <- get[(Site1[List[(String, Int)]],
                Site2[List[(String, String, Int)]])]
     // Les sites sont implicites
     // d21 = d1._1 map ({ case (d,i) => (d,i) })
     d21 = map(d1._1) { case (d, i) => (d, i) }
     // d22 = d1._2 map ({ case (n,a,i) => (n,i) })
     d22 = map(d1._2) { case (n, a, i) => (n, i) }
     // d31 = d22 filter ({case (n,i) =>
     //                     List("Chuck", "Bob").exists({ _ == n }) })
     d31 = filter(d22) { case (n, i) =>
       List("Bob", "Chuck") exists { _ == n } }
     // d32 = unFrag1(d21,d31)
     // d32 = join(d21,d31) // Doesn't type check
     d32 = join(d21.move(s0), d31.move(s0))
     // FIXME: following also type checks!
     // d321 = join(d21, d31.move(s1))
     // d322 = join(d21.move(s2), d31)
   } yield d32)
}
