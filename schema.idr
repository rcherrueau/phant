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


-- An attribute of the database is a paire of a name and a type
Attribute: Type
Attribute = (String, U)

-- A specific attribute for indexing
Id : Attribute
Id = ("Id", NAT)

-- Schema that describes the type of the database
Schema : Type
Schema = List Attribute

----------------------------------------------------------- Predicates
-- -- s ⊆ s'
-- data Sub : Schema -> Schema -> Type where
--      Stop : Sub [] s'
--      Pop  : Sub s s' -> {auto p: Elem a s'} -> Sub (a :: s) s'

-- getElem : {l : List a} -> Elem v l -> a
-- getElem _ {v} = v

-- getSub : (s' : Schema) -> Sub s s' -> Schema
-- getSub s' Stop        = []
-- getSub s' (Pop sub {p}) = (getElem p) :: (getSub s' sub)

-- -- lemmma_subInduct : (s,s' : Schema) -> Sub s s' = Sub (a :: s) (a :: s')
-- -- lemmma_subInduct s s' = Refl

-- -- subIdent : (s : Schema) -> Sub s s
-- -- subIdent s         = subIdem s s
-- --   where
-- --   subIdem : (s1 : Schema) -> (s2 : Schema) -> Sub s1 s2
-- --   subIdem []        s2 = Stop
-- --   subIdem (x :: xs) s2 with (subIdem xs s2)
-- --     subIdem (x :: [])        s2 | Stop = Pop Stop {p=Here}
-- --     subIdem (x :: (a :: ys)) s2 | (Pop y {p}) = ?subIdem_rhs_2_rhs_2



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

fragWP : (s : Schema) -> (s' : Schema) -> {auto inc : Include s s'} ->
         ((ls : Schema ** Elem Id ls), (rs: Schema ** Elem Id rs))
fragWP s s' = let ls = s
                  rs = s' \\ s
              in (indexingWP ls, indexingWP rs)

frag : (s : Schema) -> (s' : Schema) -> {auto inc : Include s s'} -> (Schema, Schema)
frag s s' {inc} = let res = fragWP s s' {inc}
                  in map getWitness res

-- FIXME: falsy implementation: product then delete of Id
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

type : Attribute -> U
type = snd

names : Schema -> List String
names = fst . unzip

types : Schema -> List U
types = snd . unzip
