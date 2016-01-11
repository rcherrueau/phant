module phant.utils

import public Data.List

%default total
%access public

infix 5 @@

-- List Inclusion.
namespace inclusion
  -- Inclusion predicate
  --
  -- Asserts that the elements of the first list are elements of the
  -- second list.
  -- Axiom of power set:
  -- https://en.wiktagedia.org/wiki/Axiom_of_power_set
  Include : List a -> List a -> Type
  Include xs ys = (z : _) -> Elem z xs -> Elem z ys

  ------------------------------------------------------------ Utils
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

  ------------------------------------------------------------ Props
  -- Reduction of the Include predicate
  includeReduc : Include (x :: xs) ys -> Include xs ys
  includeReduc xxsIncYs = \z,zInXs => xxsIncYs z (There zInXs)

  -- Include from a singleton list
  includeSingleton : Elem a l -> Include [a] l
  includeSingleton p = \z,zInZ => rewrite (elemSingleton zInZ) in p

  includeSingleton' : a -> {auto p : Elem a l} -> Include [a] l
  includeSingleton' _ {p} = includeSingleton p

  -- data Singleton : List a -> Type where
  --   Single : (v : a) -> Singleton [v]

  -- singleNonEmpty : Singleton l -> NonEmpty l
  -- singleNonEmpty (Single x) = IsNonEmpty

  -- singleIsHead : (s : Singleton l) -> l = [head {ok=singleNonEmpty s} l]
  -- singleIsHead (Single x) = Refl

  -- makeSingle : (l : List a) -> NonEmpty l -> Singleton  [(head l)]
  -- makeSingle [] IsNonEmpty impossible
  -- makeSingle (x :: xs) _ = (Single x)

  -- includeSingle : (l : List a) ->
  --                 {auto ok : NonEmpty l} ->
  --                 {default (makeSingle l ok) single : Singleton l} ->
  --                 {auto elem : Elem (head {ok=singleNonEmpty single} l) l'} -> Include l l'
  -- includeSingle _ {single} {elem} = rewrite (singleIsHead single) in includeSingleton elem

  -- Include of a list with self
  includeSelf : (l : List a) -> Include l l
  includeSelf l = \z,zINl => zINl

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
namespace tag
  Tag : Type
  Tag = String

  -- abstract -- to keep constructor private
  -- TODO: rename @ as Tagged. @@ as @. Make it instance of Functor
  data Tagged : (tag : Tag) -> (a : Type) -> Type where
    (@@) : (v : a) -> (tag : Tag) -> Tagged tag a

  getVal : Tagged tag a -> a
  getVal (v @@ tag) = v

  getTag : Tagged tag a -> Tag
  getTag _ {tag} = tag

  instance Functor (Tagged tag) where
      map m x = let v  = getVal x
                    tag = getTag x
                in (m v) @@ tag

  setTag : (tag' : Tag) -> Tagged tag t -> Tagged tag' t
  setTag tag' (v @@ tag) = v @@ tag'

namespace other
  map : (a -> b) -> (a, a) -> (b, b)
  map f (x, y) = (f x, f y)

  map2 : (a -> b) -> (c -> d) -> (a, c) -> (b, d)
  map2 f g (a, c) = (f a, g c)

  liftSigma : {m : Type -> Type} -> (f : a -> m a) -> (v : a ** p) -> (v : m a ** p)
  liftSigma f (x ** pf) = (f x ** pf)
