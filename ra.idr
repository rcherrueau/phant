module phant.ra

import schema
import utils
import crypt

import Data.List
import Debug.Trace

%default total
%access public

namespace expr
  data Expr : U -> Type where
    -- ExprElU : {u : U} -> (v : a) -> Expr u
    -- ExprPAIR  : (Pair (el x) (el y)) -> Expr (PAIR x y)
    -- Type
    ExprU     : (u : U) -> Expr u
    ExprUNIT  : Expr UNIT
    ExprNAT   : Nat -> Expr NAT
    ExprTEXT  : String -> Expr TEXT
    ExprREAL  : Double -> Expr REAL
    ExprBOOL  : Bool -> Expr BOOL
    ExprCRYPT : {u : U} -> AES (el u) -> Expr (CRYPT u)
    -- Operation
    ExprEq    : Eq (el a) => Expr a -> Expr a -> Expr BOOL
    ExprGtEq  : Ord (el a) => Expr a -> Expr a -> Expr BOOL
    ExprElem  : Eq (el a) => Expr a -> Expr (SCH s) -> Expr BOOL
    ExprNot   : Expr BOOL -> Expr BOOL
    -- Schema
    ExprSCH     : (s : Schema) -> Expr (SCH s)
    ExprUnion   : Expr $ SCH s -> Expr $ SCH s -> Expr $ SCH s
    ExprDiff    : Expr $ SCH s -> Expr $ SCH s' -> Expr $ SCH s
    ExprProduct : Expr $ SCH s -> Expr $ SCH s' -> Expr $ SCH (s * s')
    ExprProject : (sproj : Schema) -> Expr $ SCH s -> Expr $ SCH (intersect sproj s)
    -- ExprSelect  : {s : Schema} -> (a : Attribute) -> (Expr (getU a) -> Expr BOOL) ->
    --               {auto elem : Elem a s} -> Expr $ SCH s -> Expr $ SCH s
    ExprDrop    : (sproj : Schema) -> Expr $ SCH s -> Expr $ SCH (s \\ sproj)
    ExprCount   : (scount : Schema) ->
                  {default (includeSingleton Here) inc : Include scount s} ->
                  Expr $ SCH s -> Expr $ SCH (count scount s {inc})

  -- Operation
  (==) : Eq (el a) => Expr a -> Expr a -> Expr BOOL
  (==) = ExprEq

  (>=) : Ord (el a) => Expr a -> Expr a -> Expr BOOL
  (>=) = ExprGtEq

  elem : Eq (el a) => Expr a -> Expr (SCH s) -> Expr BOOL
  elem = ExprElem

  not : Expr BOOL -> Expr BOOL
  not = ExprNot

  encrypt : Crypt (el u) (AES (el u)) => Key -> (el u) -> Expr (CRYPT u)
  encrypt k x = ExprCRYPT (encrypt k x)

  union : Expr $ SCH s -> Expr $ SCH s -> Expr $ SCH s
  union = ExprUnion

  diff : Expr $ SCH s -> Expr $ SCH s' -> Expr $ SCH s
  diff = ExprDiff

  (*) : Expr $ SCH s -> Expr $ SCH s' -> Expr $ SCH (s * s')
  (*) = ExprProduct

  π : (sproj : Schema) -> Expr $ SCH s -> Expr $ SCH (intersect sproj s)
  π = ExprProject

  -- σ : {s : Schema} -> (a : Attribute) -> (Expr (getU a) -> Expr BOOL) ->
  --        {auto elem : Elem a s} -> Expr $ SCH s -> Expr $ SCH s
  -- σ = assert_total ExprSelect

  drop : (sproj : Schema) -> Expr $ SCH s -> Expr $ SCH (s \\ sproj)
  drop = ExprDrop

  count : (scount : Schema) ->
          {default (includeSingleton Here) inc : Include scount s} ->
          Expr $ SCH s -> Expr $ SCH (count scount s {inc})
  count = ExprCount
  -- Implicit conversion for dsl
  -- -- λΠ> the (Expr (PAIR NAT (PAIR NAT UNIT))) (1,1,())
  -- implicit pairPAIR : (Pair (el x) (el y)) -> Expr (PAIR x y)
  -- pairPAIR = ExprPAIR

  implicit unitUNIT : () -> Expr UNIT
  unitUNIT _ = ExprUNIT

  implicit natNAT : Nat -> Expr NAT
  natNAT = ExprNAT

  implicit stringTEXT : String -> Expr TEXT
  stringTEXT = ExprTEXT

  implicit doubleREAL : Double -> Expr REAL
  doubleREAL = ExprREAL

  implicit boolBOOL : Bool -> Expr BOOL
  boolBOOL = ExprBOOL

  implicit aesCRYPT : AES (el u) -> Expr (CRYPT u)
  aesCRYPT = ExprCRYPT

  implicit schemaSCH : (l : Schema) -> Expr (SCH l)
  schemaSCH = ExprSCH

  -- evalExpr : Expr u -> (el u)
  -- evalExpr (ExprPAIR p) = p
  -- evalExpr ExprUNIT = ()
  -- evalExpr (ExprNAT k) = k
  -- evalExpr (ExprTEXT s) = s
  -- evalExpr (ExprREAL x) = x
  -- evalExpr (ExprBOOL x) = x
  -- evalExpr (ExprCRYPT x) = x
  -- evalExpr (ExprLIST xs) = xs
  -- evalExpr (x == y) = (evalExpr x) == (evalExpr y)
  -- evalExpr (isIn x (ExprLIST xs)) = ?mlj -- elem x xs
  -- evalExpr (not x) = not (evalExpr x)

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
  Select  : (a : Attribute) -> (Expr (getU a) -> Expr BOOL) ->
            {auto elem : Elem a s} -> RA s -> RA s
  -- -- TODO: Join take an element to do the join
  Drop     : (sproj : Schema) -> RA s -> RA (s \\ sproj)
  -- FIXME: Do a better tatic, Something that work on each schema
  -- rather than schema singleton
  Count    : (scount : Schema) ->
             {default (includeSingleton Here) inc : Include scount s} ->
             RA s -> RA (count scount s {inc})
  -- -- Introduce
  Unit     : (s : Schema) -> RA s


union : RA s -> RA s -> RA s
union = Union

diff: RA s -> RA s' -> RA s
diff = Diff

(*) : RA s -> RA s' -> RA (s * s')
(*) = Product

π : (sproj : Schema) -> RA s -> RA (intersect sproj s)
π = Project

σ : (a : Attribute) -> (Expr (getU a) -> Expr BOOL) ->
    {auto elem : Elem a s} -> RA s -> RA s
σ = Select

drop : (sproj : Schema) -> RA s -> RA (s \\ sproj)
drop = Drop

count : (scount : Schema) ->
        {default (includeSingleton Here) inc : Include scount s} ->
        RA s -> RA (count scount s {inc})
count = Count

getSchema : RA s -> Schema
getSchema _ {s} = s

