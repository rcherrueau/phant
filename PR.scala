package phant

object PR {
  type PR[P[X],R] = Nothing

  def protect[P[_],R](r: R)(f: R => P[R]): PR[P,R] = ???
  def unit[R](r: R): PR[Raw, R] = ???
  def map[P1[_],R1,P2[_],R2](pr: PR[P1,R1])(f: P1[R1] => P2[R2]): PR[P2,R2] = ???
  def run[P[_],R](pr: PR[P,R]): R = ???
}


case class Sym[A](get: A)
case class Raw[A](get: A)

object PhantPRTest extends App {
  import spire.algebra._
  import spire.implicits._

  val db: List[(String, String, String)] = List(
    ("2014-01-01", "Bob",   "a"),
    ("2014-01-02", "Chuck", "b"),
    ("2014-01-03", "Bob",   "c"),
    ("2014-01-04", "Chuck", "d"),
    ("2014-01-05", "Bob",   "e"),
    ("2014-01-06", "Bob",   "e"),
    ("2014-01-07", "Bob",   "e"),
    ("2014-01-08", "Bob",   "f"),
    ("2014-01-09", "Chuck", "b"),
    ("2014-01-10", "Chuck", "g"))

  // Two can keep a secret:
  object Scenar1 {
    val frag1: List[(Int, String)] =
      db.zipWithIndex.map { case ((d,_,_), v) => (v+1, d) }
    val frag2: List[(Int, String, String)] =
      db.zipWithIndex.map { case ((_,n,a), v) => (v+1, n, a) }
  }

  // Two can keep a secret + Symmetric encryption:
  object Scenar2 {
    val split1: List[(Int, String)] =
      db.zipWithIndex.map { case ((d,_,_), v) => (v+1, d) }
    val split2: List[(Int, String, String)] =
      db.zipWithIndex.map { case ((_,n,a), v) => (v+1, n, a) }

    val frag1: List[(Int, String)] = split1
    val frag2: List[(Int, Sym[String], String)] =
      split2 map { case (v,n,a) => (v, Sym(n), a) }
  }

  // Multiple fragments
  object Scenar3 {
    val frag1: List[(Int, String)] =
      db.zipWithIndex.map { case ((d,_,_), v) => (v+1, d) }
    val frag2: List[(Int, String)] =
      db.zipWithIndex.map { case ((_,n,_), v) => (v+1, n) }
    val frag3: List[(Int, String)] =
      db.zipWithIndex.map { case ((_,_,a), v) => (v+1, a) }
  }

  // FIXME: In the original scenario, Alice sends a list of clients.
  // Thus, the Eq/Ord are legitimate

  // HomoEqtoOrder scenario:

  // Fragmentation protection
  object JustFrag {
    val frag1: List[(Int, String)] =
      db.zipWithIndex.map { case ((d,_,_), v) => (v+1, d) }
    val frag2: List[(Int, String, String)] =
      db.zipWithIndex.map { case ((_,n,a), v) => (v+1, n, a) }

    // SComposite
    val mostVisitedClients = {
      // Agenda operation. Has an Eq constraint on name.
      def selectMeetings[N: Eq,A](l: List[(Int, N, A)]): List[(N, A)] =
        l map { case (_, n, a) => (n, a) }

      // Stats operation. Has an Order constraint on name.
      def mostVisited[N: Order](l: List[(N, _)]): List[(N, Int)] = {
        def count[T: Eq](l: List[T]): List[(T, Int)] = l match {
          case Nil => Nil
          case hd :: tl =>
            (hd, 1 + tl.filter(hd === _).length) ::
            count(tl.filter(hd =!= _))
        }
        def sort[T: Order](l: List[(T, Int)]): List[(T, Int)] =
          l.sortWith(_ > _)

        sort(count(l.map(_._1)))
      }

      // SComposite
      mostVisited(selectMeetings(frag2))
    }
  }

  case class HesOrder[F: Order](data: F)
  implicit def hesorder[F: Order]: Order[HesOrder[F]] = new Order[HesOrder[F]] {
    override def compare(x: HesOrder[F], y: HesOrder[F]) =
      implicitly[Order[F]].compare(x.data, y.data)
  }

  // Fragmentation protection + Homomorphic Order
  object HomomorphicOrder {
    val split1: List[(Int, String)] =
      db.zipWithIndex.map { case ((d,_,_), v) => (v+1, d) }
    val split2: List[(Int, String, String)] =
      db.zipWithIndex.map { case ((_,n,a), v) => (v+1, n, a) }

    val frag1: List[(Int, String)] = split1
    val frag2: List[(Int, HesOrder[String], String)] =
      split2 map { case (v,n,a) => (v, HesOrder(n), a) }

    // SComposite
    val mostVisitedClients = {
      // Agenda operation. Has an Eq constraint on name.
      def selectMeetings[N: Eq,A](l: List[(Int, N, A)]): List[(N, A)] =
        l map { case (_, n, a) => (n, a) }

      // Stats operation. Has an Order constraint on name.
      def mostVisited[N: Order](l: List[(N, _)]): List[(N, Int)] = {
        def count[T: Eq](l: List[T]): List[(T, Int)] = l match {
          case Nil => Nil
          case hd :: tl =>
            (hd, 1 + tl.filter(hd === _).length) ::
            count(tl.filter(hd =!= _))
        }
        def sort[T: Order](l: List[(T, Int)]): List[(T, Int)] =
          l.sortWith(_ > _)

        sort(count(l.map(_._1)))
      }

      // SComposite
      mostVisited(selectMeetings(frag2))
    }
  }

  case class HesEq[F: Eq](data: F)
  implicit def heseq[F: Eq]: Eq[HesEq[F]] = new Eq[HesEq[F]] {
    override def eqv(x: HesEq[F], y: HesEq[F]) =
      implicitly[Eq[F]].eqv(x.data, y.data)
  }

  object HomomorphicEqToOrder {
    val split1: List[(Int, String)] =
      db.zipWithIndex.map { case ((d,_,_), v) => (v+1, d) }
    val split2: List[(Int, String, String)] =
      db.zipWithIndex.map { case ((_,n,a), v) => (v+1, n, a) }

    // Start with HesEq
    val frag1: List[(Int, String)] = split1
    val frag2: List[(Int, HesEq[String], String)] =
      split2 map { case (v,n,a) => (v, HesEq(n), a) }

    // SComposite
    val mostVisitedClients = {
      // Agenda operation. Has an Eq constraint on name.
      def selectMeetings[N: Eq,A](l: List[(Int, N, A)]): List[(N, A)] =
        l map { case (_, n, a) => (n, a) }

      // Stats operation. Has an Order constraint on name.
      def mostVisited[N: Order](l: List[(N, _)]): List[(N, Int)] = {
        def count[T: Eq](l: List[T]): List[(T, Int)] = l match {
          case Nil => Nil
          case hd :: tl =>
            (hd, 1 + tl.filter(hd === _).length) ::
            count(tl.filter(hd =!= _))
        }
        def sort[T: Order](l: List[(T, Int)]): List[(T, Int)] =
          l.sortWith(_ > _)

        sort(count(l.map(_._1)))
      }

      // SComposite, split the compute in two parts. First, gets
      // meetings.
      val meetings: List[(HesEq[String], String)] = selectMeetings(frag2)

      // TODO: Then, transform Name HesEq into Name HesOrder and finish the
      // calculi.
      val hesEq2HesOrder =
        meetings map { case (heseqN, a) => (HesOrder(heseqN.data), a) }

      mostVisited(hesEq2HesOrder)
    }
  }

  // PR.protect(db) { Sym(_) }
}
