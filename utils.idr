module phant.utils

import public Data.List
import public Data.Vect

%default total
%access public

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
  data Place : Type where
    AtAlice : Place
    AtApp   : Place
    AtDB    : Place
    AtFrag  : Fin n -> Place

  instance Eq Place where
    AtAlice    == AtAlice    = True
    AtApp      == AtApp      = True
    AtDB       == AtDB       = True
    (AtFrag j) == (AtFrag k) = finToNat j == finToNat k
    _          == _          = False

  instance Show Place where
    show AtAlice    = "Alice"
    show AtApp      = "App"
    show AtDB       = "DB"
    show (AtFrag x) = "Frag" ++ show (finToNat x)

  Process : Type
  Process = (Place,Place,Place)

  AppP : Process
  AppP = (AtApp, AtApp, AtApp)

  AliceP : Process
  AliceP = (AtAlice, AtAlice, AtAlice)

  recipient : Process -> Place
  recipient = fst

  caller : Process -> Place
  caller = fst . snd

  callee : Process -> Place
  callee = snd . snd

  setRecipient : Place -> Process -> Process
  setRecipient rc (_, cr, ce) = (rc , cr, ce)

  setCaller : Place -> Process -> Process
  setCaller cr (rc, _, ce) = (rc , cr, ce)

  setCallee : Place -> Process -> Process
  setCallee ce (rc, cr, _) = (rc , cr, ce)

  manageRecipient : Process -> Process -> Process
  manageRecipient (recip1, _, _) (recip2, _, _) =
                if recip1 == AtAlice || recip2 == AtAlice
                -- It should not be something different since I cannot
                -- do ExpSQL computation on other place rather than
                -- Alice and App.
                then AliceP else AppP

namespace other
  map : (a -> b) -> (a, a) -> (b, b)
  map f (x, y) = (f x, f y)

  map2 : (a -> b) -> (c -> d) -> (a, c) -> (b, d)
  map2 f g (a, c) = (f a, g c)

  liftSigma : {m : Type -> Type} -> (f : a -> m a) -> (v : a ** p) -> (v : m a ** p)
  liftSigma f (x ** pf) = (f x ** pf)

  updateBy : (a -> a -> Bool) -> (a,b) -> List (a,b) -> List (a,b)
  updateBy f p@(a,b) xs =
    case lookupBy f a xs of
      Just _  => p :: deleteBy (\(a1,_) => \(a2,_) => f a1 a2) p xs
      Nothing => (a,b) :: xs

  update : (Eq a, Eq b) => (a,b) -> List (a,b) -> List (a,b)
  update p xs = updateBy (==) p xs

  mkId : TTName -> String
  mkId (UN x)                 = x
  mkId (NS n xs)              =
    let name = mkId n
        nspace = concat (intersperse "." (reverse xs))
    in nspace ++ "." ++ name
  mkId (MN x y)               = y ++ show x
  mkId (SN x)                 = "special_name"

  ttnEq : TTName -> TTName -> Bool
  ttnEq x y = mkId x == mkId y
