module phant.ra

import schema
import table
import utils

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
  -- Set operatos
  Union    : RA s -> RA s -> RA s
  Diff     : RA s -> RA s' -> RA s
  Product  : RA s -> RA s' -> RA (s * s')
  -- Others
  Project  : (s : Schema) -> {auto inc : Include s s'} -> RA s' -> RA s
  Select   : (Row s -> Bool) -> {auto inc : Include s s'} -> RA s' -> RA s'
  Drop     : (s : Schema) -> RA s' -> {auto inc : Include s s'} -> RA (s' \\ s)
  -- Protection
  Indexing : RA s -> RA (indexing s)
  Encrypt  : (a : Attribute) -> RA s -> RA (encrypt a s)
  Decrypt  : (a : Attribute) -> RA s -> RA (decrypt a s)
  -- Introduce
  Unit     : (s : Schema) -> RA s

IndexingWP : RA s -> (ra : RA $ indexing s ** Elem Id (indexing s))
IndexingWP ra {s} = let iPos = getProof (indexingWP s)
                    in (Indexing ra ** iPos)

-- Portection
FragWP : (s : Schema) -> RA s' -> {auto inc : Include s s'} ->
         ((ral : RA (indexing s) ** Elem Id (indexing s)),
          (rar : RA (indexing (s'\\s)) ** Elem Id (indexing (s'\\s))))
FragWP s x {s'} {inc} = let ilfrag = IndexingWP (Project s x {inc})
                            irfrag = IndexingWP (Drop s x {inc})
                        in (ilfrag, irfrag)

Frag : (s : Schema) -> RA s' -> {auto inc : Include s s'} ->
       (RA (indexing s), RA (indexing (s' \\ s)))
Frag s x {s'} {inc} = let ilfrag = Indexing (Project s x {inc})
                          irfrag = Indexing (Drop s x {inc})
                      in (ilfrag, irfrag)

Defrag : {auto idInS : Elem Id s} -> {auto idInS' : Elem Id s'} -> (RA s, RA s') ->
         RA (defrag (s,s'))
Defrag (x,y) {idInS} {idInS'} =
              let lf = Drop [Id] x {inc = includeSingleton idInS}
                  rf = Drop [Id] y {inc = includeSingleton idInS'}
              in Product lf rf

DefragWP : ((ral : RA s ** Elem Id s), (rar : RA s' ** Elem Id s')) -> RA (defrag (s,s'))
DefragWP ((lf ** idInS), (rf ** idInS')) = Defrag {idInS} {idInS'} (lf,rf)
