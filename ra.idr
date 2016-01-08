module phant.ra

import schema
import table
import utils

import Data.List

%default total
%access public

mutual
  data Expr : Loc ip Attribute -> Type where
    (==)    : Eq (type a) => Expr (a@ip) -> Expr (a@ip') -> Expr  (a@(manageIp ip ip'))
    ExpAttr : {a : Attribute} -> (type a) -> (ip : Ip) -> Expr (a@ip)
    -- TODO: Make Expr on schema, so that I can directly return a Expr
    -- at Guard level and don't avec to lift it with ExprRA.
    ExpRA   : RA ([a]@ip) -> Expr (a@ip)
    ExpNat  : (n : Nat) -> Expr (("Osef", NAT)@"app")
    ExpString : (s : String) -> Expr (("Osef", (TEXT (length s)))@"app")
    ExpDouble : (d : Double) -> Expr (("Osef", REAL)@"app")
    ExpBool   : (b : Bool) -> Expr ((n, BOOL)@"app")
    ExpAES    : {u : U} -> (a : AES (el u)) -> Expr ((n,(CRYPT u))@"app")

    -- Equal : {n : String} -> {u: U} -> el u -> RA (s @ ip') -> Expr (manageIp ip ip')
    -- ExpU : Nat -> Expr "local"
    -- ExpRA : RA (s @ ip) -> Expr ip
    -- Equal : (a : Expr ip) -> (b : Expr ip') ->  Expr (manageIp ip ip')

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
    Select'  : (a : Attribute) -> (Expr (a@ip) -> Expr (a@ip')) ->
               {auto elem : Elem a s} -> RA (s @ ip) -> RA (s @ (manageIp ip ip'))
    -- -- TODO: Join take an element to do the join
    Drop     : (sproj : Schema) -> RA (s @ ip) -> RA (map (flip (\\) sproj) (s @ ip))
    -- -- Introduce
    Unit     : (sIp : Loc ip Schema) -> RA sIp
