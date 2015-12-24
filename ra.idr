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


-- Portection
Frag : (s : Schema) -> RA s' -> {auto sub : Sub s s'} ->
       ((ral : RA (indexingS s) ** Elem Id (indexingS s)),
        (rar : RA (indexingS (s'\\s)) ** Elem Id (indexingS (s'\\s))))
Frag s x {s'} = let ilfrag = Indexing (Project s x)
                    irfrag = Indexing (Drop s x)
                in (ilfrag, irfrag)

Defrag : RA s -> RA s' ->
         {auto idInS : Elem Id s} -> {auto idInS' : Elem Id s'} ->
         RA ((delete Id s) * (delete Id s'))
Defrag x y {idInS} {idInS'} = let lf = Drop [Id] x {sub=Pop Stop {p=idInS}}
                                  rf = Drop [Id] y {sub=Pop Stop {p=idInS'}}
                              in Product lf rf

Encrypt : (a : Attribute) -> RA s -> RA (encrypt a s)
Encrypt a x {s} = Unit (encrypt a s)
