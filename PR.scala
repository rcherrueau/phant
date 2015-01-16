package phant

object PhantPRTest extends App {
  import spire.algebra._
  import spire.implicits._

  // ------------------------------------------------------------ Services
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

  object Agenda {
    // Has an Eq constraint on name.
    def getMeetings[N: Eq,A](names: List[N],
                             db: List[(Int, N, A)]): List[(N, A)] =
      db filter {
        // Operation `===` comes from Eq
        case (_, n, _) => names.exists(_ === n) } map {
        case (_, n, a) => (n, a) }
  }

  object Stats {
    private def count[T: Eq](l: List[T]): List[(T, Int)] = l match {
      case Nil => Nil
      case hd :: tl =>
        // Operations `===` and `=!=` come from Eq
        (hd, 1 + tl.filter(hd === _).length) ::
        count(tl.filter(hd =!= _))
    }

    // Has an Order constraint on name.
    def mostVisited[N: Order](db: List[(N, _)]): List[(N, Int)] = {
      // Operations `<` comes from Order
      count(db.map(_._1)) sortWith (_ < _)
    }
  }

  // ----------------------------------------------------------- Scenarios
  // Fragmentation, Two can keep a secret:
  object Scenar1 {
    val split1: List[(Int, String)] =
      db.zipWithIndex.map { case ((d,_,_), v) => (v+1, d) }
    val split2: List[(Int, String, String)] =
      db.zipWithIndex.map { case ((_,n,a), v) => (v+1, n, a) }

    val frag1: List[(Int, String)] = split1
    val frag2: List[(Int, String, String)] = split2
  }

  // Fragmentation, Two can keep a secret + Symmetric encryption:
  case class Sym[A](data: A)

  object Scenar2 {
    val split1: List[(Int, String)] =
      db.zipWithIndex.map { case ((d,_,_), v) => (v+1, d) }
    val split2: List[(Int, String, String)] =
      db.zipWithIndex.map { case ((_,n,a), v) => (v+1, n, a) }

    val frag1: List[(Int, String)] = split1
    val frag2: List[(Int, Sym[String], String)] =
      split2 map { case (v,n,a) => (v, Sym(n), a) }
  }

  // Fragmentation protection
  object JustFrag {
    val split1: List[(Int, String)] =
      db.zipWithIndex.map { case ((d,_,_), v) => (v+1, d) }
    val split2: List[(Int, String, String)] =
      db.zipWithIndex.map { case ((_,n,a), v) => (v+1, n, a) }

    val frag1: List[(Int, String)] = split1
    val frag2: List[(Int, String, String)] = split2

    // SComposite
    val mostVisitedClients = {
      val names: List[String] = List("Bob", "Chuck")

      Stats.mostVisited(Agenda.getMeetings(names, frag2))
    }
  }

  println(JustFrag.mostVisitedClients)

  // Fragmentation protection + Homomorphic Order
  case class HesOrder[F: Order](data: F)
  implicit def hesorder[F: Order]: Order[HesOrder[F]] =
    new Order[HesOrder[F]] {
      override def compare(x: HesOrder[F], y: HesOrder[F]) =
        implicitly[Order[F]].compare(x.data, y.data)
  }

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
      val names: List[HesOrder[String]] =
        List(HesOrder("Bob"), HesOrder("Chuck"))

      Stats.mostVisited(Agenda.getMeetings(names, frag2))
    }
  }

  println(HomomorphicOrder.mostVisitedClients)


  // Fragmentation protection + Homomorphic Eq and Order
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
      val names: List[HesEq[String]] =
        List(HesEq("Bob"), HesEq("Chuck"))

      // Split the computation in two parts. First, gets meetings
      val meetings: List[(HesEq[String], String)] =
        Agenda.getMeetings(names, frag2)

      /// Then, transform Name HesEq into Name HesOrder
      val hesEq2HesOrder =
        meetings map { case (heseqN, a) => (HesOrder(heseqN.data), a) }

      // And finish the calculi
      Stats.mostVisited(hesEq2HesOrder)
    }
  }

  println(HomomorphicEqToOrder.mostVisitedClients)
}
