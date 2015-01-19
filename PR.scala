package phant

/** Pretected Resouce Manager
  *
  * A Protected Resource Manager `PR` optimize the impact of applying
  * multiple protection to one resource and ensure that your program
  * is correct. A `PR` is made of a Protection `P` and a Resource `R`.
  *
  * There are multiple form of protections over resources:
  * - Raw (nothing)
  * - Aes (symmetric encryption)
  * - HesEq/Order/AddMonoid/MulMonoid (homomorphic encryption)
  * - Frag (data fragmentation)
  * - Pull (owner bring back data)
  */

object Protection {
  import spire.algebra._

  // General trait for resource protection
  sealed trait Protection[R] { def data: R }

  // Symmetric encryption
  case class Aes[R](data: R) extends Protection[R]

  // Homomorphic encryption with Eq operation
  case class HesEq[R: Eq](data: R) extends Protection[R]
  implicit def heseq[R: Eq]: Eq[HesEq[R]] = new Eq[HesEq[R]] {
    override def eqv(x: HesEq[R], y: HesEq[R]) =
      implicitly[Eq[R]].eqv(x.data, y.data)
  }

  // Homomorphic encryption with Order operations
  case class HesOrder[R: Order](data: R) extends Protection[R]
  implicit def hesorder[R: Order]: Order[HesOrder[R]] =
    new Order[HesOrder[R]] {
      override def compare(x: HesOrder[R], y: HesOrder[R]) =
        implicitly[Order[R]].compare(x.data, y.data)
  }

  // Data fragmentation: We want to split the database on column. We
  // define a method span, that splits the database into a
  // prefix/suffix paire (`Chunk`) according to a predicate. A `Chunk`
  // takes the idea of HList but where Head is a Seq and tail is type
  // T.

  // Data pulling
}

object PhantPRTest extends App {
  import spire.algebra._
  import spire.implicits._
  import Protection._

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
    // Here column splitting is made in many iteration over the
    // database.
    val split1: List[(Int, String)] =
      db.zipWithIndex.map { case ((d,_,_), v) => (v, d) }
    val split2: List[(Int, String, String)] =
      db.zipWithIndex.map { case ((_,n,a), v) => (v, n, a) }

    val frag1: List[(Int, String)] = split1
    val frag2: List[(Int, String, String)] = split2
  }

  // Fragmentation, Two can keep a secret + Symmetric encryption:
  object Scenar2 {
    val split1: List[(Int, String)] =
      db.zipWithIndex.map { case ((d,_,_), v) => (v, d) }
    val split2: List[(Int, String, String)] =
      db.zipWithIndex.map { case ((_,n,a), v) => (v, n, a) }

    val frag1: List[(Int, String)] = split1
    val frag2: List[(Int, Aes[String], String)] =
      split2 map { case (v,n,a) => (v, Aes(n), a) }
  }

  // Fragmentation, multiple fragments
  object Scenar3 {
    // Here column splitting is made in one iteration over the
    // database.
    val (split1, split2, split3) =
      db.zipWithIndex.foldLeft[(List[(Int, String)],
                                List[(Int, String)],
                                List[(Int, String)])]((Nil,Nil,Nil)) {
        case ((ds,ns,as), ((d,n,a), v)) => ((v, d) :: ds,
                                            (v, n) :: ns,
                                            (v, a) :: as)
      }

    val frag1: List[(Int, String)] = split1
    val frag2: List[(Int, String)] = split2
    val frag3: List[(Int, String)] = split3
  }

  // Fragmentation protection
  object JustFrag {
    val split1: List[(Int, String)] =
      db.zipWithIndex.map { case ((d,_,_), v) => (v, d) }
    val split2: List[(Int, String, String)] =
      db.zipWithIndex.map { case ((_,n,a), v) => (v, n, a) }

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
  object HomomorphicOrder {
    val split1: List[(Int, String)] =
      db.zipWithIndex.map { case ((d,_,_), v) => (v, d) }
    val split2: List[(Int, String, String)] =
      db.zipWithIndex.map { case ((_,n,a), v) => (v, n, a) }

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
  object HomomorphicEqToOrder {
    val split1: List[(Int, String)] =
      db.zipWithIndex.map { case ((d,_,_), v) => (v, d) }
    val split2: List[(Int, String, String)] =
      db.zipWithIndex.map { case ((_,n,a), v) => (v, n, a) }

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
