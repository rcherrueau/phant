module phant.ra

import schema
import table
import utils

import Data.List
import Debug.Trace

%default total
%access public

mutual
  -- -- TODO: Make Expr on schema, so that I can directly return a
  -- -- Expr at Guard level and don't avec to lift it with ExprRA.
  -- -- Let's say that a query* of guard also always return a list of
  -- -- schema.
  data Expr : Loc ip U -> Type where
    -- (==)    : Eq (el u) => {u : U} -> Expr (u@ip) -> Expr (u@ip') -> Expr (u@(manageIp ip ip'))
    ExpAttr : {a : Attribute} -> (type a) -> (ip : Ip) -> Expr ((getU a)@ip)
    ExpU    : {u : U} -> el u -> (ip : Ip) -> Expr (u @ ip)
    ExpNat  : (n : Nat) -> Expr (NAT @ "app")
    ExpStr  : (s : String) -> Expr ((TEXT (length s))@"app")
    ExpDbl  : (d : Double) -> Expr (REAL@"app")
    ExpBool : (b : Bool) -> Expr (BOOL@"app")
    ExpAES  : {u : U} -> (a : AES (el u)) -> Expr ((CRYPT u)@"app")

  evalExpr : Expr (u @ ip) -> el u
  evalExpr (ExpAttr x ip) = x
  evalExpr (ExpU x ip)    = x
  evalExpr (ExpNat n)     = n
  evalExpr (ExpStr s)     = s
  evalExpr (ExpDbl d)     = d
  evalExpr (ExpBool b)    = b
  evalExpr (ExpAES a)     = a

  liftSch : (s : Schema) -> {auto ok : NonEmpty s} -> Type
  liftSch []                     {ok} = absurd ok
  liftSch [(n,u)]                {ok} = el u
  liftSch ((_,u) :: s@(a :: as)) {ok} = Pair (el u) (liftSch s)

  liftSchU : (s : Schema) -> {auto ok : NonEmpty s} -> U
  liftSchU []                     {ok} = absurd ok
  liftSchU [(n,u)]                {ok} = u
  liftSchU ((_,u) :: s@(a :: as)) {ok} = PAIR u (liftSchU s)
  -- mkExprSch : (s : Schema) -> {auto ok : NonEmpty s} ->

  liftExpr : (f : el u1 -> el u2) ->
              Expr (u1 @ ip) -> Expr (u2 @ ip)
  liftExpr f x {ip} = ExpU (f (evalExpr x)) ip

  liftExpr2 : (f : el u1 -> el u2 -> el u3) ->
              Expr (u1 @ ip1) -> Expr (u2 @ ip2) -> Expr (u3 @ (manageIp ip1 ip2))
  liftExpr2 f x y {ip1} {ip2} =
    trace ("ip1,ip2: " ++ ip1 ++ "," ++ ip2) (
      ExpU (f (evalExpr x) (evalExpr y)) (manageIp ip1 ip2))

  liftExpr3 : (f : el u1 -> el u2 -> el u3 -> el u4) ->
              Expr (u1 @ ip1) -> Expr (u2 @ ip2) -> Expr (u3 @ ip3) ->
              Expr (u4 @ (manageIp (manageIp ip1 ip2) ip3))
  liftExpr3 f x y z {ip1} {ip2} {ip3} =
    ExpU (f (evalExpr x) (evalExpr y) (evalExpr z))
         (manageIp (manageIp ip1 ip2) ip3)

  const : Expr (a @ ip1) -> Expr (b @ ip2) -> Expr (a @ ip2)
  const x y {a} {ip2} = ExpU (evalExpr) ip2

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
               {auto elem : Elem a s} -> RA (s @ ip) -> RA (s @ ip')
    -- -- TODO: Join take an element to do the join
    Drop     : (sproj : Schema) -> RA (s @ ip) -> RA (map (flip (\\) sproj) (s @ ip))
    -- -- Introduce
    Unit     : (sIp : Loc ip Schema) -> RA sIp
