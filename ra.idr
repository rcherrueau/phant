module phant.ra

import schema
import utils
import crypt

import Data.List
import Debug.Trace

%default total
%access public

-- myPCs : List PC
-- myPCs = []

myPCs : List PC
myPCs = [[("Name",TEXT)],[("Date",NAT),("Addr",TEXT)]]

mipi : Tagged ip1 Schema -> Tagged ip2 Schema -> Tag
mipi (x @@ ip1) (y @@ ip2) = mip x ip1 y ip2 myPCs

mipiExpr : Tagged ip1 Schema -> Tagged ip2 Schema -> Tag
mipiExpr t1 t2 = case mipi t1 t2 of
                   "local" => Local
                   _       => App

mipii : Tag -> Schema -> Tag
mipii ip s with (isCons (getInnerPCs s myPCs))
  mipii ip s | False = ip
  mipii ip s | True = Local

namespace expr
  data Expr : Tagged ip U -> Type where
    -- Type
    ExprU     : (u : U) -> Expr (u @@ App)
    ExprUNIT  : Expr (UNIT @@ App)
    ExprNAT   : Nat -> Expr (NAT @@ App)
    ExprTEXT  : String -> Expr (TEXT @@ App)
    ExprREAL  : Double -> Expr (REAL @@ App)
    ExprBOOL  : Bool -> Expr (BOOL @@ App)
    ExprCRYPT : {u : U} -> AES (el u) -> Expr ((CRYPT u) @@ App)
    -- -- Operation
    -- order matter with ip :(
    ExprEq    : Eq (el a) => Expr (a @@ ip2) -> Expr (a @@ ip1) -> Expr (BOOL @@ (mip2 ip1 ip2))
    ExprGtEq  : Ord (el a) => Expr (a @@ ip2) -> Expr (a @@ ip1) -> Expr (BOOL @@ (mip2 ip1 ip2))
    ExprElem  : Eq (el a) => Expr (a @@ ip2) -> Expr ((SCH s) @@ ip1) -> Expr (BOOL @@ (mip2 ip1 ip2))
    ExprNot   : Expr (BOOL @@ ip) -> Expr (BOOL @@ ip)
    -- -- Schema
    ExprSCH     : (s : Schema) -> Expr ((SCH s) @@ App)
    -- TODO: localized at App
    -- ExprUnion   : Expr $ SCH s -> Expr $ SCH s -> Expr $ SCH s
    -- ExprDiff    : Expr $ SCH s -> Expr $ SCH s' -> Expr $ SCH s
    ExprProduct : Expr $ SCH s @@ ip1 -> Expr $ SCH s' @@ ip2 -> Expr $ SCH (s * s') @@ (mipiExpr (s @@ ip1)
                                                                                              (s' @@ ip2))
    -- ExprProject : (sproj : Schema) -> Expr $ (SCH s) @@ ip -> Expr $ (SCH (intersect sproj s)) @@ App
    -- ExprSelect  : {s : Schema} -> (a : Attribute) -> (Expr (getU a) -> Expr BOOL) ->
    --               {auto elem : Elem a s} -> Expr $ SCH s -> Expr $ SCH s
    -- ExprDrop    : (sproj : Schema) -> Expr $ SCH s -> Expr $ SCH (s \\ sproj)
    ExprCount   : (scount : Schema) ->
                  {default (includeSingleton Here) inc : Include scount s} ->
                  Expr $ SCH s @@ ip -> Expr $ SCH (count scount s {inc}) @@ App


  -- Operation
  (==) : Eq (el a) => Expr (a @@ ip2) -> Expr (a @@ ip1) -> Expr (BOOL @@ (mip2 ip1 ip2))
  (==) = ExprEq

  (>=) : Ord (el a) => Expr (a @@ ip2) -> Expr (a @@ ip1) -> Expr (BOOL @@ (mip2 ip1 ip2))
  (>=) = ExprGtEq

  elem : Eq (el a) => Expr (a @@ ip2) -> Expr ((SCH s) @@ ip1) -> Expr (BOOL @@ (mip2 ip1 ip2))
  elem = ExprElem

  not : Expr (BOOL @@ ip) -> Expr (BOOL @@ ip)
  not = ExprNot

  encrypt : Crypt (el u) (AES (el u)) => Key -> (el u) -> Expr ((CRYPT u) @@ App)
  encrypt k x = ExprCRYPT (encrypt k x)

  -- union : Expr $ SCH s -> Expr $ SCH s -> Expr $ SCH s
  -- union = ExprUnion

  -- diff : Expr $ SCH s -> Expr $ SCH s' -> Expr $ SCH s
  -- diff = ExprDiff

  (*) : Expr $ SCH s @@ ip1 -> Expr $ SCH s' @@ ip2 ->
        Expr $ SCH (s * s') @@ (mipiExpr (s @@ ip1) (s' @@ ip2))
  (*) = ExprProduct

  -- project : (sproj : Schema) -> Expr $ (SCH s) @@ ip -> Expr $ (SCH (intersect sproj s)) @@ App
  -- project = ExprProject

  -- select : {s : Schema} -> (a : Attribute) -> (Expr (getU a) -> Expr BOOL) ->
  --        {auto elem : Elem a s} -> Expr $ SCH s -> Expr $ SCH s
  -- select = assert_total ExprSelect

  -- drop : (sproj : Schema) -> Expr $ SCH s -> Expr $ SCH (s \\ sproj)
  -- drop = ExprDrop

  count : (scount : Schema) ->
          {default (includeSingleton Here) inc : Include scount s} ->
          Expr $ SCH s @@ ip -> Expr $ SCH (count scount s {inc}) @@ App
  count = ExprCount
  -- -- Implicit conversion for dsl
  -- -- -- λΠ> the (Expr (PAIR NAT (PAIR NAT UNIT))) (1,1,())
  -- -- implicit pairPAIR : (Pair (el x) (el y)) -> Expr (PAIR x y)
  -- -- pairPAIR = ExprPAIR

  implicit unitUNIT : () -> Expr (UNIT @@ App)
  unitUNIT _ = ExprUNIT

  implicit natNAT : Nat -> Expr (NAT @@ App)
  natNAT = ExprNAT

  implicit stringTEXT : String -> Expr (TEXT @@ App)
  stringTEXT = ExprTEXT

  implicit doubleREAL : Double -> Expr (REAL @@ App)
  doubleREAL = ExprREAL

  implicit boolBOOL : Bool -> Expr (BOOL @@ App)
  boolBOOL = ExprBOOL

  implicit aesCRYPT : AES (el u) -> Expr ((CRYPT u) @@ App)
  aesCRYPT = ExprCRYPT

  implicit schemaSCH : (l : Schema) -> Expr ((SCH l) @@ App)
  schemaSCH = ExprSCH

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
data RA : Tagged ip Schema -> Type where
  -- Set operators
  Union    : RA (s @@ ip1) -> RA (s @@ ip2) -> RA (s @@ (mipi (s @@ ip1) (s @@ ip2)))
  Diff     : RA (s @@ ip1) -> RA (s' @@ ip2) -> RA (s @@ (mipi (s @@ ip1) (s' @@ ip2)))
  Product  : RA (s @@ ip1) -> RA (s' @@ ip2) -> RA ((s * s') @@ (mipi (s @@ ip1) (s' @@ ip2)))
  -- Others
  Project  : (sproj : Schema) -> RA (s @@ ip) -> RA ((intersect sproj s) @@ ip)
--   -- -- TODO: Select on an element with specific operation
  Select  : (a : Attribute) -> (Expr ((getU a) @@ ip) -> Expr (BOOL @@ ipExpr)) ->
            {auto elem : Elem a s} -> RA (s @@ ip) -> RA (s @@ (mipi (s @@ ip) (s @@ ipExpr)))
--   -- -- TODO: Join take an element to do the join
  Drop     : (sproj : Schema) -> RA (s @@ ip) -> RA ((s \\ sproj) @@ ip)
--   -- FIXME: Do a better tatic, Something that work on each schema
--   -- rather than schema singleton
  Count    : (scount : Schema) ->
             {default (includeSingleton Here) inc : Include scount s} ->
             RA (s @@ ip) -> RA ((count scount s {inc}) @@ ip)
--   -- -- Introduce
  Unit     : (s : Schema) -> (ip : Tag) -> RA (s @@ ip)


union : RA (s @@ ip1) -> RA (s @@ ip2) -> RA (s @@ (mipi (s @@ ip1) (s @@ ip2)))
union = Union

diff : RA (s @@ ip1) -> RA (s' @@ ip2) -> RA (s @@ (mipi (s @@ ip1) (s' @@ ip2)))
diff = Diff

(*): RA (s @@ ip1) -> RA (s' @@ ip2) -> RA ((s * s') @@ (mipi (s @@ ip1) (s' @@ ip2)))
(*) = Product

project : (sproj : Schema) -> RA (s @@ ip) -> RA ((intersect sproj s) @@ ip)
project = Project

select : (a : Attribute) -> (Expr ((getU a) @@ ip) -> Expr (BOOL @@ ipExpr)) ->
         {auto elem : Elem a s} ->
         RA (s @@ ip) -> RA (s @@ (mipi (s @@ ip) (s @@ ipExpr)))
select = Select

drop : (sproj : Schema) -> RA (s @@ ip) -> RA ((s \\ sproj) @@ ip)
drop = Drop

count : (scount : Schema) ->
        {default (includeSingleton Here) inc : Include scount s} ->
        RA (s @@ ip) -> RA ((count scount s {inc}) @@ ip)
count = Count

getSchema : RA (s @@ ip) -> Schema
getSchema _ {s} = s

getIp : RA (s @@ ip) -> Tag
getIp _ {ip} = ip
