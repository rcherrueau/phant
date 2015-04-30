package phant

sealed trait Site[A, S[A] <: Site[A,S]] { self: S[A] =>
  def get: A
  def apply[B](b: B): S[B]
}
case class Site0[A](get: A) extends Site[A, Site0] {
  def apply[B](b: B): Site0[B] = Site0(b)
}
case class Site1[A](get: A) extends Site[A, Site1] {
  def apply[B](b: B): Site1[B] = Site1(b)
}
case class Site2[A](get: A) extends Site[A, Site2] {
  def apply[B](b: B): Site2[B] = Site2(b)
}

object Site {
  def s0 = Site0("")
  def s1 = Site1("")
  def s2 = Site2("")
}
