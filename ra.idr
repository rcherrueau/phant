module phant.ra

import schema
import table
import utils

import Data.List

%default total
%access public

mutual
  -- -- TODO: Make Expr on schema, so that I can directly return a Expr
  -- -- at Guard level and don't avec to lift it with ExprRA.
  data Expr : Loc ip U -> Type where
    -- (==)    : Eq (el u) => {u : U} -> Expr (u@ip) -> Expr (u@ip') -> Expr (u@(manageIp ip ip'))
    ExpAttr : {a : Attribute} -> (type a) -> (ip : Ip) -> Expr ((getU a)@ip)
    ExpU    : {u : U} -> el u -> (ip : Ip) -> Expr (u @ ip)
    ExpF1   : {u1,u2 : U} -> (f : el u1 -> el u2) ->
              Expr (u1 @ ip) -> Expr (u2 @ ip)
    ExpF2   : {u1,u2,u3 : U} -> (f : el u1 -> el u2 -> el u3) ->
              Expr (u1 @ ip1) -> Expr (u2 @ ip2) -> Expr (u3 @ (manageIp ip1 ip2))
    ExpRA   : RA ([a]@ip) -> Expr ((getU a)@ip)
    ExpNat  : (n : Nat) -> Expr (NAT @ "app")
    ExpStr  : (s : String) -> Expr ((TEXT (length s))@"app")
    ExpDbl  : (d : Double) -> Expr (REAL@"app")
    ExpBool : (b : Bool) -> Expr (BOOL@"app")
    ExpAES  : {u : U} -> (a : AES (el u)) -> Expr ((CRYPT u)@"app")

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
    UnsafeSelect : (Row (getVal sIp') -> Bool) ->
                   {default (includeSelf (getVal sIp'))
                    inc : Include (getVal sIp') (getVal sIp)} ->
                   RA sIp -> RA sIp
    Select   : (a : Attribute) -> (type a -> Bool) ->
               {auto elem : Elem a (getVal sIp)} -> RA sIp -> RA sIp
    Select'  : (a : Attribute) -> (Expr ((getU a)@ip) -> Expr (BOOL@ip')) ->
               {auto elem : Elem a s} -> RA (s @ ip) -> RA (s @ (manageIp ip ip'))
    -- -- TODO: Join take an element to do the join
    Drop     : (sproj : Schema) -> RA (s @ ip) -> RA (map (flip (\\) sproj) (s @ ip))
    -- -- Introduce
    Unit     : (sIp : Loc ip Schema) -> RA sIp
