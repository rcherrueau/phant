package phant

import spire.algebra._, spire.implicits._

// ------------------------------------------------------------ Protection
trait Rsc
trait Protected extends Rsc

object Rsc {
  def toHEq[R](r: Raw[R])(implicit eq: Eq[R]): HEq[R] =
    HEq(r.get)
}

// Raw
class Raw[R](val get: R) extends Rsc {
  override def toString(): String = s"Raw($get)"
}
object Raw {
  def apply[R](r: R) = new Raw(r)

  implicit def eq[R: Eq]: Eq[Raw[R]] = new Eq[Raw[R]] {
    override def eqv(x: Raw[R], y: Raw[R]) =
      implicitly[Eq[R]].eqv(x.get, y.get)
  }

  implicit def order[R: Order]: Order[Raw[R]] = new Order[Raw[R]] {
    override def compare(x: Raw[R], y: Raw[R]) =
      implicitly[Order[R]].compare(x.get, y.get)
  }

  implicit def plus[R: AdditiveMonoid]: AdditiveMonoid[Raw[R]] =
    new AdditiveMonoid[Raw[R]] {
      override def zero: Raw[R] =
        Raw(implicitly[AdditiveMonoid[R]].zero)

      override def plus(x: Raw[R], y: Raw[R]) =
        Raw(implicitly[AdditiveMonoid[R]].plus(x.get, y.get))
    }

  implicit def times[R: MultiplicativeMonoid]:
      MultiplicativeMonoid[Raw[R]] =
    new MultiplicativeMonoid[Raw[R]] {
      override def one: Raw[R] =
        Raw(implicitly[MultiplicativeMonoid[R]].one)

      override def times(x: Raw[R], y: Raw[R]) =
        Raw(implicitly[MultiplicativeMonoid[R]].times(x.get, y.get))
    }

  implicit def toRaw[R](r: R): Raw[R] = Raw(r)
}

// AES
class AES[R](val get: R) extends Protected {
  override def toString(): String = s"AES($get)"
}
object AES {
  def apply[R](r: R) = new AES(r)
}

trait HES[R] extends Protected

// Homomorphic Eq
class HEq[R: Eq](val get: R) extends HES[R] {
  override def toString(): String = s"HEq($get)"
}
object HEq {
  def apply[R: Eq](r: R) = new HEq(r)

  implicit def heq[R: Eq]: Eq[HEq[R]] = new Eq[HEq[R]] {
    override def eqv(x: HEq[R], y: HEq[R]) =
      implicitly[Eq[R]].eqv(x.get, y.get)
  }
}

// Homomorphic Order
class HOrder[R: Order](get: R) extends HEq[R](get) {
  override def toString(): String = s"HOrder($get)"
}
object HOrder {
  def apply[R: Order](r: R) = new HOrder(r)

  implicit def horder[R: Order]: Order[HOrder[R]] =
    new Order[HOrder[R]] {
      override def compare(x: HOrder[R], y: HOrder[R]) =
        implicitly[Order[R]].compare(x.get, y.get)
    }
}
