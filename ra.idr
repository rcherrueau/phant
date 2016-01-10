module phant.ra

import schema
import utils
import crypt

import Data.List
import Debug.Trace

%default total
%access public

liftSch : (s : Schema) -> Type
liftSch []                     = ()
liftSch [(n,u)]                = el u
liftSch ((_,u) :: s@(a :: as)) = Pair (el u) (liftSch s)

-- liftSchU : (s : Schema) -> U
-- liftSchU []                     = UNIT
-- liftSchU [(n,u)]                = u
-- liftSchU ((_,u) :: s@(a :: as)) = PAIR u (liftSchU s)

data Expr : U -> Type where
  -- ExprElU : {u : U} -> (v : a) -> Expr u
  ExprU     : (u : U) -> Expr u
  ExprUNIT  : Expr UNIT
  ExprNAT   : Nat -> Expr NAT
  ExprTEXT  : (s : String) -> Expr (TEXT (length s))
  ExprREAL  : Double -> Expr REAL
  ExprBOOL  : Bool -> Expr BOOL
  ExprCRYPT : {u : U} -> AES (el u) -> Expr (CRYPT u)
  -- ExprPAIR  : (Pair (el x) (el y)) -> Expr (PAIR x y)
  -- (==) x y = ExprBOOL $ (evalExpr x) == (evalExpr y)
  ExprEq    : Eq (el a) => Expr a -> Expr a -> Expr BOOL
  ExprGtEq  : Ord (el a) => Expr a -> Expr a -> Expr BOOL
  -- elem x (ExprLIST xs) = ExprBOOL $ elem (evalExpr x) xs
  ExprElem  : Eq (el a) => Expr a -> Expr (SCH s) -> Expr BOOL
  -- not (ExprBOOL x) = ExprBOOL $ not x
  ExprNot   : Expr BOOL -> Expr BOOL
  -- Schema
  ExprSCH     : (s : Schema) -> Expr (SCH s)
  ExprUnion   : Expr $ SCH s -> Expr $ SCH s -> Expr $ SCH s
  ExprDiff    : Expr $ SCH s -> Expr $ SCH s' -> Expr $ SCH s
  ExprProduct : Expr $ SCH s -> Expr $ SCH s' -> Expr $ SCH (s * s')
  ExprProject : (sproj : Schema) -> Expr $ SCH s -> Expr $ SCH (intersect sproj s)

implicit unitUNIT : () -> Expr UNIT
unitUNIT _ = ExprUNIT

implicit natNAT : Nat -> Expr NAT
natNAT = ExprNAT

implicit stringTEXT : (s : String) -> Expr (TEXT (length s))
stringTEXT = ExprTEXT

implicit doubleREAL : Double -> Expr REAL
doubleREAL = ExprREAL

implicit boolBOOL : Bool -> Expr BOOL
boolBOOL = ExprBOOL

implicit aesCRYPT : AES (el u) -> Expr (CRYPT u)
aesCRYPT = ExprCRYPT

-- implicit listLIST : List (el u) -> Expr (LIST u)
-- listLIST = ExprLIST

-- -- λΠ> the (Expr (PAIR NAT (PAIR NAT UNIT))) (1,1,())
-- implicit pairPAIR : (Pair (el x) (el y)) -> Expr (PAIR x y)
-- pairPAIR = ExprPAIR

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
  Select  : (a : Attribute) -> (Expr (getU a) -> Expr BOOL) ->
            {auto elem : Elem a s} -> RA s -> RA s
  -- -- TODO: Join take an element to do the join
  Drop     : (sproj : Schema) -> RA s -> RA (s \\ sproj)
  -- -- Introduce
  Unit     : (s : Schema) -> RA s

getSchema : RA s -> Schema
getSchema _ {s} = s

---------- Proofs ----------

-- phant.ra.mlj = proof
--   intros
--   let v = (evalExpr x)
--   let elemV = (elem v)
--   refine elemV
--   exact xs
