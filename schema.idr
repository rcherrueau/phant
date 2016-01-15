||| Schema for Relational Algebra.
|||
||| A schema describes the type of a table. It consists of a set of
||| pairs of column names and types. We do not allow any type to occur
||| in a Schema, but restrict ourself to the Univers (U, el)
module phant.schema

import crypt
import utils

import Data.List
import Data.Vect

%default total
%access public

-- Universe for Database allowed types (both `U` and `el`)
--
-- Every data constructor of U corresponds to a type.
namespace universe
  data U = UNIT
         | NAT
         | TEXT
         | REAL
         | BOOL
         | CRYPT U
         | SCH (List (String, U))
         -- | PAIR U U
         -- | LIST U
         -- | HOME U

  mutual
    liftSch : (s : List (String, U)) -> Type
    liftSch []                     = ()
    liftSch [(n,u)]                = assert_total $ el u
    liftSch ((_,u) :: s@(a :: as)) = assert_total $ Pair (el u) (liftSch s)

    -- Decoding function
    el : U -> Type
    el UNIT         = ()
    el NAT          = Nat
    el TEXT         = String
    el REAL         = Double
    el BOOL         = Bool
    el (CRYPT U)    = (AES (el U))
    el (SCH l)      = List (liftSch l)
    -- el (PAIR U1 U2) = (Pair (el U1) (el U2))
    -- el (LIST U)     = List (el U)
    -- el (HOME U)  = el U

  -- -- Returns the inner u if any
  -- private
  -- getU : U -> U
  -- getU (CRYPT u) = u
  -- -- getU (HOME  u) = u
  -- getU u         = u

  data InUfamily : Type -> Type where
    IsUNIT  : InUfamily Unit
    IsNAT   : InUfamily Nat
    IsTEXT  : InUfamily String
    IsREAL  : InUfamily Double
    IsBOOL  : InUfamily Bool
    IsCRYPT : {auto p: InUfamily u} -> InUfamily (AES u)
    IsSCH   : InUfamily (List (String, U))
    -- IsPAIR  : {auto p1 : InUfamily u1} -> {auto p2 : InUfamily u2} ->
    --           InUfamily (Pair u1 u2)
    -- IsLIST  : {auto p: InUfamily u} -> InUfamily (List u)

  le : (t : Type) -> {auto p: InUfamily t} -> U
  le _ {p = IsUNIT} = UNIT
  le _ {p = IsNAT}  = NAT
  le _ {p = IsTEXT} = TEXT
  le _ {p = IsREAL} = REAL
  le _ {p = IsBOOL} = BOOL
  le _ {p = IsCRYPT {p} {u}} = CRYPT (le u {p})
  le _ {p = IsSCH}  = SCH []
  -- le _ {p = IsPAIR {p1} {p2} {u1} {u2}} = PAIR (le u1 {p=p1}) (le u2 {p=p2})
  -- le _ {p = IsLIST {p} {u}} = LIST (le u {p})

  instance Eq U where
    UNIT == UNIT             = True
    NAT == NAT               = True
    TEXT == TEXT             = True
    REAL == REAL             = True
    BOOL == BOOL             = True
    (CRYPT x) == (CRYPT y)   = x == y
    -- FIXME: why not total?
    -- (SCH x) == (SCH y)       = assert_total x == y
    -- (LIST x) == (LIST y)     = x == y
    -- (PAIR w x) == (PAIR y z) = w == y && x == y
    -- (HOME x) == (HOME y) = x == y
    _ == _                   = False

  -- instance DecEq U where
  --   decEq UNIT UNIT           = Yes Refl
  --   decEq NAT NAT             = Yes Refl
  --   decEq (TEXT x)  (TEXT y)  with (decEq x y)
  --     decEq (TEXT x)  (TEXT x)  | (Yes Refl)
  --                             = Yes Refl
  --     decEq (TEXT x)  (TEXT y)  | (No contra)
  --                             = No (\txIsTy =>
  --                                     contra $ cong txIsTy {f = getNat})
  --       where
  --       getNat : U -> Nat
  --       getNat (TEXT x) = x
  --       getNat _        = Z
  --   decEq REAL      REAL      = Yes Refl
  --   decEq BOOL      BOOL      = Yes Refl
  --   decEq (CRYPT x) (CRYPT y) with (decEq x y)
  --     decEq (CRYPT x) (CRYPT x) | (Yes Refl)
  --                               = Yes Refl
  --     decEq (CRYPT x) (CRYPT y) | (No contra)
  --                               = No (\cxIsCy => contra $ cong cxIsCy {f = getU})
  --   decEq (LIST x) (LIST y) = ?TODO1
  --   decEq (PAIR w x) (PAIR y z) = ?TODO2
  --   -- decEq (HOME x)  (HOME y)  with (decEq x y)
  --   --   decEq (HOME x)  (HOME x)  | (Yes Refl)
  --   --                           = Yes Refl
  --   --   decEq (HOME x)  (HOME y)  | (No contra)
  --   --                           = No (\hxIsHy =>
  --   --                                   contra $ cong hxIsHy {f = getU})
  --   -- For other case, I should go like D. Christiansen
  --   -- https://github.com/david-christiansen/IdrisSqlite/blob/master/type-provider-demo/SQLiteTypes.idr
  --   decEq x         y         = No believemeNotEq
  --       where
  --       postulate believemeNotEq : x = y -> Void


-- An attribute of the database is a paire of a name and a type
Attribute: Type
Attribute = (String, U)

-- A specific attribute for indexing
Id : Attribute
Id = ("Id", NAT)

-- A specific attribute for counting
Count : Attribute
Count = ("Count", NAT)

-- Schema that describes the type of the database
Schema : Type
Schema = List Attribute

-- Utils opreration on schema
-- TODO: In addtion to the product (*), make a join that takes two
-- elem `Elem a s1` & `Elem a s2` to do the join.
(*) : Schema -> Schema -> Schema
(*) x y = nub (x ++ y)

indexingWP : Schema -> (s : Schema ** Elem Id s)
indexingWP []        = ([Id] ** Here)
indexingWP (a :: as) with (indexingWP as)
  indexingWP (a :: as) | (as' ** p) = (a :: as' ** There p)

indexing : Schema -> Schema
indexing = getWitness . indexingWP

fragWP : (sproj : Schema) -> (s : Schema) ->
         ((sl : Schema ** Elem Id sl), (sr: Schema ** Elem Id sr))
fragWP sproj s = let sl = intersect sproj s
                     sr = s \\ sproj
                 in (indexingWP sl, indexingWP sr)

-- frag : (sproj : Schema) -> (s : Schema) -> (Schema, Schema)
-- frag sproj = (map getWitness) . (fragWP sproj)

frag : (sprojs : List Schema) -> (s : Schema) -> Vect (S (length sprojs)) Schema
frag [] s        = [indexing s]
frag (x :: xs) s = (indexing $ intersect x s) :: (frag xs (s \\ x))

count : (scount : Schema) -> (s : Schema) ->
        {auto inc : Include scount s} -> Schema
count scount s = scount ++ [Count]

-- FIXME: false implementation: product then delete of Id. This is a
-- false implementation regarding to what should be done at
-- operational level on tuple of a database. However, this is OK for a
-- schema since we are only interested in the result. Despite this, we
-- should change the implementation to be equivalent of what is
-- happening over the tuple to help the type checker during the
-- unification.
defrag : (Schema, Schema) -> Schema
defrag = (uncurry (*)) . (map (delete Id))

defragWP : ((ls : Schema ** Elem Id ls), (rs: Schema ** Elem Id rs)) -> Schema
defragWP = defrag . (map getWitness)

encrypt : Attribute -> Schema -> Schema
encrypt a []        = []
encrypt a (x :: xs) with (a == x)
  encrypt a     (x :: xs) | False = x :: (encrypt a xs)
  encrypt (n,u) (x :: xs) | True  = (n, CRYPT u) :: xs

encryptF : Attribute -> (fId : Fin n) -> Vect n Schema -> Vect n Schema
encryptF a FZ     (x :: xs) = (encrypt a x) :: xs
encryptF a (FS k) (x :: xs) = x :: (encryptF a k xs)

getU : Attribute -> U
getU = snd

decrypt : Attribute -> Schema -> Schema
decrypt (n, (CRYPT u')) [] = []
decrypt (n, (CRYPT u')) (x :: xs) with ((n, (CRYPT u')) == x)
  decrypt (n, (CRYPT u')) (x :: xs) | False = x :: (decrypt (n, (CRYPT u')) xs)
  decrypt (n, (CRYPT u')) (x :: xs) | True = (n, u') :: xs
decrypt _ s = s

isEncrypted : Attribute -> Bool
isEncrypted (_, CRYPT _) = True
isEncrypted _            = False

name : Attribute -> String
name = fst

type : Attribute -> Type
type = el . snd

names : Schema -> List String
names = fst . unzip

types : Schema -> List Type
types = map type

getUs : Schema -> List U
getUs = snd . unzip

getSchema : (fId : Fin n) -> Vect n Schema -> Schema
getSchema FZ     (x :: xs) = x
getSchema (FS k) (x :: xs) = getSchema k xs


-- liftSchU : (s : Schema) -> U
-- liftSchU []                     = UNIT
-- liftSchU [(n,u)]                = u
-- liftSchU ((_,u) :: s@(a :: as)) = PAIR u (liftSchU s)
