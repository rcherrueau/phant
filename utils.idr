module phant.utils

import Data.List

%default total


-- List Inclusion.
namespace inclusion
  -- Inclusion predicate
  --
  -- Asserts that the elements of the first list are elements of the
  -- second list.
  -- Axiom of power set:
  -- https://en.wikipedia.org/wiki/Axiom_of_power_set
  Include : List a -> List a -> Type
  Include xs ys = (z : _) -> Elem z xs -> Elem z ys

  -- Reduction of the Include predicate
  includeReduc : Include (x :: xs) ys -> Include xs ys
  includeReduc xxsIncYs = \z,zInXs => xxsIncYs z (There zInXs)

  -- Being an element of a singleton list implies to be that singleton
  elemSingleton : Elem z [x] -> z = x
  elemSingleton Here           = Refl
  elemSingleton (There zInNil) = absurd zInNil

  -- Being an element of a non empty list and not being the fisrt
  -- element implies to be an element of the tail.
  elemTail : (z = hd -> Void) -> Elem z (hd :: tl) -> Elem z tl
  -- (z ∈ [hd] => z = hd) ∧ z ≠ hd
  elemTail nzIsHd zInHdTl   {tl = []} = let zIsHd = elemSingleton zInHdTl in
                                        void $ nzIsHd zIsHd
  -- (z ∈ z :: tl => z = hd) ∧ z ≠ hd
  elemTail nzIsHd Here      {tl}      = void $ nzIsHd Refl
  -- z ∈ _ :: tl => z ∈ tl
  elemTail nzIsHd (There p) {tl}      = p

  -- Is the elements of the first list are elements of the second
  -- list.
  isIncluded : DecEq a => (xs : List a) -> (ys : List a) ->
               Dec (Include xs ys)
  -- This definition seems correct since I cannot provide any `z` due
  -- to the empty `xs`.
  isIncluded []        ys         = Yes (\z,zInXs => absurd zInXs)
  -- First check if `xs` is included in `ys` or not.
  isIncluded (x :: xs) ys with (isIncluded xs ys)
    isIncluded (x :: xs) ys | (No nxsIncYs) =
                               No $ notTailInc nxsIncYs
      where
      notTailInc : (Include xs ys -> Void) -> Include (x :: xs) ys -> Void
      notTailInc nxsIncYs xxsIncYs = nxsIncYs (\z,zInXs =>
                                                 xxsIncYs z (There zInXs))

    isIncluded (x :: xs) ys | (Yes xsIncYs) with (isElem x ys)
      -- Then manage `x` is an element of `ys` or not.
      isIncluded (x :: xs) ys | (Yes xsIncYs) | (Yes xInYs) =
                               Yes $ headInTailInc xInYs xsIncYs
        where
        headInTailInc : Elem x ys -> Include xs ys -> Include (x :: xs) ys
        headInTailInc xInYs xsIncYs = \z,zInXxs => case decEq z x of
                         No nzIsX => let zInXs = elemTail nzIsX zInXxs in
                                     xsIncYs z zInXs
                         Yes zIsX => rewrite zIsX in xInYs

      isIncluded (x :: xs) ys | (Yes xsIncYs) | (No nxInYs) =
                               No $ notHeadIn nxInYs
        where
        notHeadIn : (Elem x ys -> Void) -> Include (x :: xs) ys -> Void
        notHeadIn nxInYs xxsIncYs = let xInYs = xxsIncYs x Here in
                                    nxInYs xInYs

  -- -- The result of the intersection between two list `xs` and `ys` is
  -- -- both included in `xs` and `ys`.
  -- intersectIncluded : (Eq a, DecEq a) => (xs, ys : List a) ->
  --                     (Include (intersect xs ys) xs,
  --                      Include (intersect xs ys) ys)
  -- intersectIncluded xs ys =
  --   let zsIncXs = \z,zInZs => fst $ elemInter xs ys z zInZs in
  --   let zsIncYs = \z,zInZs => snd $ elemInter xs ys z zInZs in
  --   (zsIncXs, zsIncYs)
