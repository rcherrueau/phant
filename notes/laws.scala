import shapeless._

trait laws {
  type Id = Int
  val db: List[(String, Unit)]

  //---------------------------------------------------------------- Id
  def frag[A,B](l: List[(A,B)]): (List[(A,Id)], List[(B, Id)])
  def unfrag[A,B](f: (List[(A,Id)], List[(B, Id)])): List[(A,B)]

  // -- identity
  identity(db):  List[(String, Unit)]
  unfrag(frag(db)): List[(String, Unit)]
  // --

  def pi1[A,B]:((A,B)) => A
  def pi2[A,B]:((A,B)) => B
  def rmId[A]:((A, Id)) => A

  //------------------------------------------------------------ Project
  def project[T,C](l: List[T])(f: T => C): List[C]

  // -- project on 1
  project(unfrag(frag(db)))(pi1): List[String]
  project(frag(db)._1)(rmId):     List[String]
  // --

  // -- project on 2
  project(unfrag(frag(db)))(pi2): List[Unit]
  project(frag(db)._2)(rmId):     List[Unit]
  // --

  //------------------------------------------------------------ Select
  def select[T](l: List[T])(f1: T => Boolean): List[T]
  def lift[T](f: T => Boolean): ((T, Id)) => Boolean
  val p1 = (s: String) => true
  val p2 = (u: Unit) => true
  val p12 = (t: (String, Unit)) => true
  val (f1, f2) = frag(db)

  // -- select p1 @ Pi1, p2 @ Pi2, p12 @ Pi12
  {
    select(unfrag(frag(db))) {
      case (s,u) => p1(s) && p2(u) && p12((s,u))
    } : List[(String, Unit)]

    // Two possibilities: 1) I use rmId, 2) I lift p*
    val ff1 = select(f1) (lift(p1)): List[(String, Id)]
    val ff2 = select(f2) (lift(p2)): List[(Unit, Id)]
      select(unfrag((ff1, ff2))) (p12): List[(String, Unit)]
  }
  // --

  // -- select p1 @ Pi1
  {
    select(unfrag(frag(db))) { case (s,u) => p1(s) }: List[(String, Unit)]
    val ff1 = select(f1) (lift(p1)): List[(String, Id)]
    unfrag((ff1, f2)): List[(String, Unit)]
  }
  // --

}
