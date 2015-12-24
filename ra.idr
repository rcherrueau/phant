module phant.ra

import schema
import table

import Data.List

%default total

-- A query expression (Relation Algebra)
--
-- An expression of `RA s` corresponds to a query that will return a
-- table with schema `s`. Operations are those ones of relational
-- algebra.
--
-- Relational algebra uses set union, set difference and cartesian
-- product from set theory, but adds additional constraints. Unions
-- and difference must be /union-compatible/, i.e., the two relations
-- must have the *same set of attributes*.
--
-- Cartesion product flattens the schema.
-- See, https://en.wikipedia.org/wiki/Relational_algebra#Set_operators
data RA : Schema -> Type where
  -- Introduce
  Unit    : (s : Schema) -> RA s
  -- Set operatos
  Union   : RA s -> RA s -> RA s
  Diff    : RA s -> RA s' -> RA s
  Product : RA s -> RA s' -> RA (s * s')
  -- Others
  Project : (s : Schema) -> RA s' -> {auto sub : Sub s s'} -> RA s
  Select  : (Row s -> Bool) -> RA s -> RA s
  Drop    : (s : Schema) -> RA s' -> {auto sub : Sub s s'} -> RA (s' \\ s)

-- Indexing : RA s -> (r : RA s' ** Elem Id s')
Indexing : RA s -> (ra : RA $ indexingS s ** Elem Id (indexingS s))
Indexing x {s} = let isWPos = indexing s
                     is = getWitness isWPos
                     iPos = getProof isWPos
                 in (Unit is ** iPos)


-- Utils
defragS : (Schema, Schema) -> Schema
defragS (s1, s2) = (delete Id s1) * (delete Id s2)

getSubS : (f : (Schema, Schema)) -> (s : Schema) ->
          (sub : Sub s (defragS f)) ->
          (Schema, Schema)

-- Portection
Frag : (s : Schema) -> RA s' -> {auto sub : Sub s s'} ->
       ((ral : RA (indexingS s) ** Elem Id (indexingS s)),
        (rar : RA (indexingS (s'\\s)) ** Elem Id (indexingS (s'\\s))))
Frag s x {s'} = let ilfrag = Indexing (Project s x)
                    irfrag = Indexing (Drop s x)
                in (ilfrag, irfrag)

Defrag : {auto idInS : Elem Id s} -> {auto idInS' : Elem Id s'} ->
         (RA s, RA s') ->
         RA (defragS (s,s'))
Defrag (x,y) {idInS} {idInS'} =
              let lf = Drop [Id] x {sub=Pop Stop {p=idInS}}
                  rf = Drop [Id] y {sub=Pop Stop {p=idInS'}}
              in Product lf rf

Encrypt : (a : Attribute) -> RA s -> RA (encrypt a s)
Encrypt a x {s} = Unit (encrypt a s)

Decrypt : (a : Attribute) -> RA s -> RA (decrypt a s)
Decrypt a x {s} = Unit (decrypt a s)


--

-- l1 : (f : (Schema , Schema)) -> (s : Schema) ->
--      (sub : Sub s (defragS f)) ->
--      (idInFl : Elem Id (fst f)) -> (idInFr : Elem Id (snd f)) ->
--      ((Project s) . (Defrag {idInS=idInFl} {idInS'=idInFr})) = ()

and : (Row s -> Bool) -> (Row s' -> Bool) -> (Row (defragS (s,s')) -> Bool)
and f g r = ?and_rhs

onBoth : (Row s -> Bool) -> (Row s' -> Bool) -> (RA s, RA s') -> (RA s, RA s')
onBoth f g x = let l = Select f (fst x)
                   r = Select g (snd x)
               in (l,r)

l2 : (f : (Schema, Schema)) ->
     (pl : Row (fst f) -> Bool) -> (pr : Row (snd f) -> Bool) ->
     (idInFl : Elem Id (fst f)) -> (idInFr : Elem Id (snd f)) ->
     (Select (and pl pr)) . (Defrag {idInS=idInFl} {idInS'=idInFr}) =
     (Defrag {idInS=idInFl} {idInS'=idInFr}) . (onBoth pl pr)
l2 f pl pr idInFl idInFr = ?l2_rhs




-- (Project s . Defrag) = (Defrag .
