module phant.ra

import schema
import table
import utils

import Data.List
import Debug.Trace

%default total
%access public

liftSch : (s : Schema) -> Type
liftSch []                     = ()
liftSch [(n,u)]                = el u
liftSch ((_,u) :: s@(a :: as)) = Pair (el u) (liftSch s)

-- data Expr : U -> Type where
--   ExprNat : Nat -> Expr NAT
--   ExprStr : (s : String) -> Expr (TEXT (length s))
--   ExprReal : Double -> Expr REAL
--   ExprBool : Bool -> Expr BOOL
--   ExprCrypt : {u : U} -> AES (el u) -> Expr (CRYPT u)

-- liftExpr2 : (el a -> el b -> el c) -> Expr a -> Expr b -> Expr c
-- liftExpr2 f x y = ?liftExpr2_rhs

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
  -- -- TODO: Select on an element with specific operation
  Select  : (a : Attribute) -> (type a -> Bool) ->
            {auto elem : Elem a s} -> RA s -> RA s
  -- -- TODO: Join take an element to do the join
  Drop     : (sproj : Schema) -> RA s -> RA (s \\ sproj)
  -- -- Introduce
  Unit     : (s : Schema) -> RA s
