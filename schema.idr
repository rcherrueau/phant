||| Schema for Relational Algebra.
|||
||| A schema describes the type of a table. It consists of a set of
||| pairs of column names and types. We do not allow any type to occur
||| in a Schema, but restrict ourself to the Univers (U, el)
module phant.schema

import public crypt
import utils

import Data.List

%default total
%access public

data Truc : List Type -> Type

-- Universe for Database allowed types (both `U` and `el`)
--
-- Every data constructor of U corresponds to a type.
namespace universe
  data U = NAT
         | TEXT Nat
         | REAL
         | BOOL
         | CRYPT U
         | PAIR U U
         -- | HOME U

  -- Decoding function
  el : U -> Type
  el NAT          = Nat
  el (TEXT n)     = String
  el REAL         = Double
  el BOOL         = Bool
  el (CRYPT U)    = (AES (el U))
  el (PAIR U1 U2) = (Pair (el U1) (el U2))
  -- el (HOME U)  = el U

  -- Returns the inner u if any
  private
  getU : U -> U
  getU (CRYPT u) = u
  -- getU (HOME  u) = u
  getU u         = u

  instance Eq U where
    NAT == NAT           = True
    (TEXT x) == (TEXT y) = x == y
    REAL == REAL         = True
    BOOL == BOOL         = True
    -- (HOME x) == (HOME y) = x == y
    (CRYPT x) == (CRYPT y)  = x == y
    _ == _               = False

  instance DecEq U where
    decEq NAT       NAT       = Yes Refl
    decEq (TEXT x)  (TEXT y)  with (decEq x y)
      decEq (TEXT x)  (TEXT x)  | (Yes Refl)
                              = Yes Refl
      decEq (TEXT x)  (TEXT y)  | (No contra)
                              = No (\txIsTy =>
                                      contra $ cong txIsTy {f = getNat})
        where
        getNat : U -> Nat
        getNat (TEXT x) = x
        getNat _        = Z
    decEq REAL      REAL      = Yes Refl
    decEq BOOL      BOOL      = Yes Refl
    -- decEq (HOME x)  (HOME y)  with (decEq x y)
    --   decEq (HOME x)  (HOME x)  | (Yes Refl)
    --                           = Yes Refl
    --   decEq (HOME x)  (HOME y)  | (No contra)
    --                           = No (\hxIsHy =>
    --                                   contra $ cong hxIsHy {f = getU})
    decEq (CRYPT x) (CRYPT y) with (decEq x y)
      decEq (CRYPT x) (CRYPT x) | (Yes Refl)
                                = Yes Refl
      decEq (CRYPT x) (CRYPT y) | (No contra)
                                = No (\cxIsCy => contra $ cong cxIsCy {f = getU})
    -- For other case, I should go like D. Christiansen
    -- https://github.com/david-christiansen/IdrisSqlite/blob/master/type-provider-demo/SQLiteTypes.idr
    decEq x         y         = No believemeNotEq
        where
        postulate believemeNotEq : x = y -> Void


-- An attribute of the database is a paire of a name and a type
Attribute: Type
Attribute = (String, U)

-- A specific attribute for indexing
Id : Attribute
Id = ("Id", NAT)

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

frag : (sproj : Schema) -> (s : Schema) -> (Schema, Schema)
frag sproj = (map getWitness) . (fragWP sproj)

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

decrypt : Attribute -> Schema -> Schema
decrypt a []        = []
decrypt a (x :: xs) with (a == x)
  decrypt a     (x :: xs) | False = x :: (decrypt a xs)
  decrypt (n,u) (x :: xs) | True  = (n, getU u) :: xs

isEncrypted : Attribute -> Bool
isEncrypted (_, CRYPT _) = True
isEncrypted _            = False

name : Attribute -> String
name = fst

getU : Attribute -> U
getU = snd

type : Attribute -> Type
type = el . snd

names : Schema -> List String
names = fst . unzip

types : Schema -> List Type
types = map type

getUs : Schema -> List U
getUs = snd . unzip
