package phant

object nat {
    sealed trait Nat {
      type This >: this.type <: Nat
      type Fold[U, F[_ <: U] <: U, Z <: U] <: U
      type ++ = Succ[This]

      // Combining Term- and Type-Level
      def value: Int

      type +[X <: Nat] =
        Fold[Nat, ({ type λ[N <: Nat] = Succ[N] })#λ, X]
      // Hybrid operation: Term- & Type-level. Thus our `+` method is
      // correctly typed.
      def  +[X <: Nat](n: X): +[X] =
        // Here, we have to wrap the int operation in
        // the correct Nat.
        Nat._unsafe[+[X]](value + n.value)

      def ++ : ++ = Succ(this.value)

      // -- For HList # Span
      def --  = if (this.value == 0) throw new NoSuchElementException("_0 --")
                else if (this.value == 1) Zero
                else Succ(value - 1)

      type GT_0[R, T <: R, F <: R] <: R
      type LTEq_0[R, T <: R, F <: R] <: R

      type -- <: Nat
    }
    object Nat {
      def _unsafe[N <: Nat](v: Int) =
        (if (v == 0) Zero else Succ(v)).asInstanceOf[N]
    }

    final object Zero extends Nat {
      type This = Zero
      type Fold[U, F[_ <: U] <: U, Z <: U] = Z

      def value = 0

      // -- For HList # Span
      type GT_0[R, T <: R, F <: R] = F
      type LTEq_0[R, T <: R, F <: R] = T
      type -- = Nothing
    }
    type Zero = Zero.type

    final case class Succ[N <: Nat](val value: Int) extends Nat {
      type This = Succ[N]
      type Fold[U, F[_ <: U] <: U, Z <: U] = F[N#Fold[U, F, Z]]

      // -- For HList # Span
      type GT_0[R, T <: R, F <: R] = T
      type LTEq_0[R, T <: R, F <: R] = F
      type -- = N
    }

    type _0 = Zero
    type _1 = _0 # ++
    type _2 = _1 # ++
    type _3 = _1 # + [_2]
    type _4 = _1 # + [_3]
    type _5 = _1 # + [_4]
    type _6 = _1 # + [_5]

    lazy val _0: _0 = Zero
    lazy val _1: _1 = Succ[_0](1)
    lazy val _2: _2 = Succ[_1](2)
    lazy val _3: _3 = Succ[_2](3)
    lazy val _4: _4 = Succ[_3](4)
    lazy val _5: _5 = Succ[_4](5)
    lazy val _6: _6 = Succ[_5](6)
}
