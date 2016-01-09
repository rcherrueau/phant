module phant.ra

import schema
import table
import utils

import Data.List
import Debug.Trace

%default total
%access public

liftSch : (s : Schema) -> {auto ok : NonEmpty s} -> Type
liftSch []                     {ok} = absurd ok
liftSch [(n,u)]                {ok} = el u
liftSch ((_,u) :: s@(a :: as)) {ok} = Pair (el u) (liftSch s)

liftLoc2 : (f : a -> b -> c) -> Loc ip1 a -> Loc ip2 b -> Loc (manageIp ip1 ip2) c
liftLoc2 f ((@) a ip1) ((@) b ip2) = (f a b) @ (manageIp ip1 ip2)

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
data RA : Loc ip Schema -> Type where
  -- Set operators
  Union    : RA (s @ ip1) -> RA (s @ ip2) -> RA (s @ (manageIp ip1 ip2))
  Diff     : RA (s @ ip1) -> RA (s' @ ip2) -> RA (s @ (manageIp ip1 ip2))
  Product  : RA (s @ ip1) -> RA (s' @ ip2) -> RA ((s * s') @ (manageIp ip1 ip2))
  -- Others
  Project  : (sproj : Schema) -> RA (s @ ip) -> RA (map (intersect sproj) (s @ ip))
  -- -- TODO: Select on an element with specific operation
  Select  : (a : Attribute) -> (Loc ip (type a) -> Loc ip' Bool) ->
            {auto elem : Elem a s} -> RA (s @ ip) -> RA (s @ ip')
  -- -- TODO: Join take an element to do the join
  Drop     : (sproj : Schema) -> RA (s @ ip) -> RA (map (flip (\\) sproj) (s @ ip))
  -- -- Introduce
  Unit     : (sIp : Loc ip Schema) -> RA sIp

getIp : RA (s @ ip) -> Ip
getIp _ {ip} = ip

getSchema : RA (s @ ip) -> Schema
getSchema _ {s} = s
