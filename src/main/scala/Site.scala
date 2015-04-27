package phant

sealed trait Site[A, S[X] <: Site[X,S]] { self: S[A] =>
  def get: A
  def apply[B](b: B): S[B] = this(b)
}
case class Site0[A](get: A) extends Site[A, Site0]
case class Site1[A](get: A) extends Site[A, Site1]
case class Site2[A](get: A) extends Site[A, Site2]

object Site {
  def s0 = Site0("")
  def s1 = Site1("")
  def s2 = Site2("")
}
