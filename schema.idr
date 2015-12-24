||| Schema for Relational Algebra.
|||
||| A schema describes the type of a table. It consists of a set of
||| pairs of column names and types. We do not allow any type to occur
||| in a Schema, but restrict ourself to the Univers (U, el)
module phant.schema

import crypt

import Data.List

%default total
%access public

-- Universe for Database allowed types (both `U` and `el`)
--
-- Every data constructor of U corresponds to a type.
namespace universe
  data U = NAT
         | TEXT Nat
         | REAL
         | BOOL
         | CRYPT U
         | HOME U


  -- Decoding function
  el : U -> Type
  el NAT       = Nat
  el (TEXT n)  = String
  el REAL      = Double
  el BOOL      = Bool
  el (CRYPT U) = (AES (el U))
  el (HOME U)  = el U

  -- Returns the inner u if any
  private getU : U -> U
  getU (CRYPT u) = u
  getU (HOME  u) = u
  getU u         = u


  instance Eq U where
    NAT == NAT           = True
    (TEXT x) == (TEXT y) = x == y
    REAL == REAL         = True
    BOOL == BOOL         = True
    (HOME x) == (HOME y) = x == y
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
    decEq (HOME x)  (HOME y)  with (decEq x y)
      decEq (HOME x)  (HOME x)  | (Yes Refl)
                              = Yes Refl
      decEq (HOME x)  (HOME y)  | (No contra)
                              = No (\hxIsHy =>
                                      contra $ cong hxIsHy {f = getU})
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


Attribute: Type
Attribute = (String, U)

-- A specific attribute for indexing
Id : Attribute
Id = ("Id", NAT)


Schema : Type
Schema = List Attribute

-- Predicates
-- s ⊆ s'
data Sub : Schema -> Schema -> Type where
     Stop : Sub [] s'
     Pop  : Sub s s' -> {auto p: Elem a s'} -> Sub (a :: s) s'

-- Utils opreration on schema
(*) : Schema -> Schema -> Schema
(*) x y = nub (x ++ y)

indexing : Schema -> (s : Schema ** Elem Id s)
indexing []        = ([Id] ** Here)
indexing (a :: as) with (indexing as)
  indexing (a :: as) | (as' ** p) = (a :: as' ** There p)

indexingS : Schema -> Schema
indexingS = getWitness . indexing

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

name : Attribute -> String
name = fst

type : Attribute -> U
type = snd

names : Schema -> List String
names = fst . unzip

types : Schema -> List U
types = snd . unzip
