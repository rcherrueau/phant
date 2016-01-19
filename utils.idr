module phant.utils

import public Data.List
import public Data.Vect

%default total
%access public

infix 5 @
infix 5 @@


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

  ------------------------------------------------------------ Utils
  -- Being an element of a singleton list implies to be that singleton
  elemSingleton : with List Elem z [x] -> z = x
  elemSingleton Here           = Refl
  elemSingleton (There zInNil) = absurd zInNil

  -- Being an element of a non empty list and not being the fisrt
  -- element implies to be an element of the tail.
  elemTail : (z = hd -> Void) -> with List Elem z (hd :: tl) -> Elem z tl
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
namespace location
  Ip : Type
  Ip = String

  -- abstract -- to keep constructor private
  -- TODO: rename @ as Loc. @@ as @. Make it instance of Functor
  data Loc : (ip : Ip) -> (a : Type) -> Type where
    (@) : (v : a) -> (ip : Ip) -> Loc ip a

  getVal : Loc ip a -> a
  getVal ((@) v ip) = v

  getIp : Loc ip a -> Ip
  getIp _ {ip} = ip

  instance Functor (Loc ip) where
      map m x = let v  = getVal x
                    ip = getIp x
                in (m v) @ ip

  -- The algorithm is more complicated than this. The idea is the
  -- following.
  --
  -- > Are the two ip equals?
  -- > Yes => Keep the ip
  -- > No => Is the computation involve attributes that are inside
  -- >       the PCs?
  -- >       Yes => Set ip to local
  -- >       No  => Set ip to application
  --
  -- Unfortunately, this requires PC and schema, two information that
  -- are not available as it.
  manageIp : Ip -> Ip -> Ip
  manageIp x y = if x == "local" || y == "local" then x
                 else if x == "app" then y
                 else if y == "app" then x
                 else "local"

namespace other
  map : (a -> b) -> (a, a) -> (b, b)
  map f (x, y) = (f x, f y)

  map2 : (a -> b) -> (c -> d) -> (a, c) -> (b, d)
  map2 f g (a, c) = (f a, g c)

  liftSigma : {m : Type -> Type} -> (f : a -> m a) -> (v : a ** p) -> (v : m a ** p)
  liftSigma f (x ** pf) = (f x ** pf)

  update : (Eq a, Eq b) => (a,b) -> List (a,b) -> List (a,b)
  update (a, b) xs = case lookup a xs of
                       Just _  => (a, b) :: (delete (a, b) xs)
                       Nothing => xs

data Place : Type where
  Alice : Place
  App   : Place
  DB    : Place
  Frag  : Fin n -> Place

Process : Type
Process = (Place,Place,Place)

instance Eq Place where
  Alice    == Alice    = True
  App      == App      = True
  DB       == DB       = True
  (Frag j) == (Frag k) = finToNat j == finToNat k
  _        == _        = False

recipient : Process -> Place
recipient = fst

caller : Process -> Place
caller = fst . snd

callee : Process -> Place
callee = snd . snd

setRecipient : Place -> Process -> Process
setRecipient r (a, b, c) = (r , b, c)

AppP : Process
AppP = (App, App, App)

AliceP : Process
AliceP = (Alice, Alice, Alice)

findRecipient : Process -> Process -> Process
findRecipient (recip1, _, _) (recip2, _, _) =
  if recip1 == Alice || recip2 == Alice
  -- It should not be something different since I cannot do Exp*
  -- computation on other place rather than Alice and App.
  then (Alice,Alice,Alice) else (App,App,App)
