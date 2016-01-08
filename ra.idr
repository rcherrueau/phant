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
  -- Set operators
  Union    : RA s -> RA s -> RA s
  Diff     : RA s -> RA s' -> RA s
  Product  : RA s -> RA s' -> RA (s * s')
  -- Others
  Project  : (sproj : Schema) -> RA s -> RA (intersect sproj s)
  -- TODO: Select on an element with specific operation
  -- Select   : (Row s' -> Bool) ->
  --            {auto ok : NonEmpty s'} ->
  --            {default (|(includeSingle s' {ok}), (includeSelf s')|) inc: Include s' s} -> RA s -> RA s
  UnsafeSelect : (Row s' -> Bool) ->
                 {default (includeSelf s') inc : Include s' s} -> RA s -> RA s
  Select   : (a : Attribute) -> (type a -> Bool) ->
             {auto elem : Elem a s} -> RA s -> RA s
  -- TODO: Join take an element to do the join
  Drop     : (sproj : Schema) -> RA s -> RA (s \\ sproj)
  -- Introduce
  Unit     : (s : Schema) -> RA s

-- eval : RA s -> IO ()
-- eval (Union x y) = do putStrLn "Union"
--                       eval x
--                       eval y
-- eval (Diff x y) = do putStrLn "Diff"
--                      eval x
--                      eval y
-- eval (Product x y) = do putStrLn "Product"
--                         putStr " "
--                         eval x
--                         putStr " "
--                         eval y
-- eval (Project s x) = do putStrLn "Project"
--                         eval x
-- eval (Select f x) = do putStrLn "Select"
--                        eval x
-- eval (Drop s x) = do putStrLn "Drop"
--                      eval x
-- eval (Unit s) = putStr ""

