module phant.ra

import schema
import utils
import crypt

import Data.List
import Debug.Trace
import Data.Vect
import Effect.Default

%default total
%access public

data Place : Type where
     Alice : Place
     App   : Place
     DB    : Place
     Frag  : Fin n -> Place

instance Eq Place where
  Alice    == Alice    = True
  App      == App      = True
  DB       == DB       = True
  (Frag j) == (Frag k) = finToNat j == finToNat k
  _        == _        = False

caller : (Place,Place,Place) -> Place
caller = fst . snd

callee : (Place,Place,Place) -> Place
callee = snd . snd

recipient : (Place,Place,Place) -> Place
recipient = fst

setRecipient : Place -> (Place,Place,Place) -> (Place,Place,Place)
setRecipient r (a, b, c) = (r , b, c)

AppP : (Place, Place, Place)
AppP = (App, App, App)

AliceP : (Place, Place, Place)
AliceP = (Alice, Alice, Alice)

findRecipient : (Place,Place,Place) -> (Place,Place,Place) -> (Place,Place,Place)
findRecipient (recip1, _, _) (recip2, _, _) =
  if recip1 == Alice || recip2 == Alice
  -- It should not be something different since I cannot do Exp*
  -- computation on other place rather than Alice and App.
  then (Alice,Alice,Alice) else (App,App,App)


namespace expr
  mutual
    data Expr : U -> (Place,Place,Place) -> Type where
    --   -- ExprElU : {u : U} -> (v : a) -> Expr u
    --   -- ExprPAIR  : (Pair (el x) (el y)) -> Expr (PAIR x y)
    --   -- Type
      -- ExprU     :  (u : U) -> (p : (Place,Place,Place)) -> Expr u p
      ExprUNIT  : Expr UNIT AppP
      ExprNAT   : Nat -> Expr NAT AppP
      ExprTEXT  : String -> Expr TEXT AppP
      ExprREAL  : Double -> Expr REAL AppP
      ExprBOOL  : Bool -> Expr BOOL AppP
      ExprCRYPT : {u : U} -> AES (el u) -> Expr (CRYPT u) AppP
      ExprSCH     : (s : Schema) -> (p : (Place,Place,Place)) ->
                     Expr (SCH s) p
    --   -- Operation
      ExprEq    : Eq (el a) => Expr a p1  -> Expr a p2 -> Expr BOOL (findRecipient p1 p2)
      ExprGtEq  : Ord (el a) => Expr a p1 -> Expr a p2  -> Expr BOOL (findRecipient p1 p2)
      ExprElem  : Eq (el a) => Expr a p1 -> Expr (SCH s) p2 -> Expr BOOL (findRecipient p1 p2)
    --   ExprNot   : Expr BOOL -> Expr BOOL
    --   -- Schema
    --   ExprUnion   : Expr $ SCH s -> Expr $ SCH s -> Expr $ SCH s
    --   ExprDiff    : Expr $ SCH s -> Expr $ SCH s' -> Expr $ SCH s
      ExprProduct : Expr (SCH s) p1 -> Expr (SCH s') p2  ->
                    Expr (SCH (s * s')) (findRecipient p1 p2)
      ExprProject : (sproj : Schema) -> Expr (SCH s) p -> Expr (SCH (intersect sproj s)) p

    --   ExprSelect  : {s : Schema} -> (a : Attribute) -> (Expr (getU a) -> Expr BOOL) ->
    --                 {auto elem : Elem a s} -> Expr $ SCH s -> Expr $ SCH s
    --   ExprDrop    : (sproj : Schema) -> Expr $ SCH s -> Expr $ SCH (s \\ sproj)
      ExprCount   : (scount : Schema) ->
                    {default (includeSingleton Here) inc : Include scount s} ->
                    Expr (SCH s) p -> Expr (SCH (count scount s {inc})) p
      ExprPutP    : (p : (Place,Place,Place)) -> Expr a p' -> Expr a p


    setRecipient : (p : Place) -> Expr a ppp -> Expr a (setRecipient p ppp)
    setRecipient p expr {ppp} = let ppp' = setRecipient p ppp
                                in ExprPutP ppp' expr

    givemeExpr : Default (el u) => (u : U) -> (p : (Place,Place,Place)) -> Expr u p
    givemeExpr UNIT      p = ExprPutP p $ ExprUNIT
    givemeExpr NAT       p = ExprPutP p $ ExprNAT Z
    givemeExpr TEXT      p = ExprPutP p $ ExprTEXT ""
    givemeExpr REAL      p = ExprPutP p $ ExprREAL 0.0
    givemeExpr BOOL      p = ExprPutP p $ ExprBOOL True
    givemeExpr (CRYPT x) p = let e = the (el u)
                             ExprPutP p $ ExprCRYPT ?mlkj
    givemeExpr (SCH s)   p = ExprSCH s p

    -- Operation
    -- (==) : Eq (el a) => Expr a -> Expr a -> Expr BOOL
    -- (==) = ExprEq

    -- (>=) : Ord (el a) => Expr a -> Expr a -> Expr BOOL
    -- (>=) = ExprGtEq

    -- elem : Eq (el a) => Expr a -> Expr (SCH s) -> Expr BOOL
    -- elem = ExprElem

    -- not : Expr BOOL -> Expr BOOL
    -- not = ExprNot

    const : Expr a  p1 -> Expr b p2 -> Expr a p1
    const a b = a

    encrypt : Crypt (el u) (AES (el u)) => Key -> (el u) -> Expr (CRYPT u) AppP
    encrypt k x = ExprCRYPT (encrypt k x)

    -- union : Expr $ SCH s -> Expr $ SCH s -> Expr $ SCH s
    -- union = ExprUnion

    -- diff : Expr $ SCH s -> Expr $ SCH s' -> Expr $ SCH s
    -- diff = ExprDiff

    -- (*) : Expr $ SCH s -> Expr $ SCH s' -> Expr $ SCH (s * s')
    -- (*) = ExprProduct

    -- project : (sproj : Schema) -> Expr $ SCH s -> Expr $ SCH (intersect sproj s)
    -- project = ExprProject

    -- select : {s : Schema} -> (a : Attribute) -> (Expr (getU a) -> Expr BOOL) ->
    --        {auto elem : Elem a s} -> Expr $ SCH s -> Expr $ SCH s
    -- select = assert_total ExprSelect

    -- drop : (sproj : Schema) -> Expr $ SCH s -> Expr $ SCH (s \\ sproj)
    -- drop = ExprDrop

    -- count : (scount : Schema) ->
    --         {default (includeSingleton Here) inc : Include scount s} ->
    --         Expr $ SCH s -> Expr $ SCH (count scount s {inc})
    -- count = ExprCount
    -- -- Implicit conversion for dsl
    -- -- -- λΠ> the (Expr (PAIR NAT (PAIR NAT UNIT))) (1,1,())
    -- -- implicit pairPAIR : (Pair (el x) (el y)) -> Expr (PAIR x y)
    -- -- pairPAIR = ExprPAIR

    -- implicit unitUNIT : () -> Expr UNIT
    -- unitUNIT _ = ExprUNIT

    -- implicit natNAT : Nat -> Expr NAT
    -- natNAT = ExprNAT

    -- implicit stringTEXT : String -> Expr TEXT
    -- stringTEXT = ExprTEXT

    -- implicit doubleREAL : Double -> Expr REAL
    -- doubleREAL = ExprREAL

    -- implicit boolBOOL : Bool -> Expr BOOL
    -- boolBOOL = ExprBOOL

    -- implicit aesCRYPT : AES (el u) -> Expr (CRYPT u)
    -- aesCRYPT = ExprCRYPT

    -- implicit schemaSCH : (l : Schema) -> Expr (SCH l)
    -- schemaSCH = ExprSCH

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
-- An expression of `RA s` correcipientonds to a query that will return a
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
data RA : Schema -> (Place,Place,Place) -> Type where
  -- Set operators
  -- Union    : RA s  -> RA s  -> RA s
  -- Diff     : RA s  -> RA s' -> RA s
  -- Product  : RA s  -> RA s' -> RA (s * s')
  -- Others
  -- Project  : (sproj : Schema) -> RA s -> RA (intersect sproj s)
  -- Dans mon context, j'enleve le s puis je remet le
  Project  : (sproj : Schema) -> RA s p -> RA (intersect sproj s) p
  -- TODO: Select on an element with specific operation
  Select  : (a : Attribute) -> (Expr (getU a) p  -> Expr BOOL p'') ->
            {auto elem : Elem a s} -> RA s p -> RA s p
  -- -- TODO: Join take an element to do the join
  -- Drop     : (sproj : Schema) -> RA s  -> RA (s \\ sproj)
  -- -- FIXME: Do a better tatic, Something that work on each schema
  -- -- rather than schema singleton
  Count    : (scount : Schema) ->
             {default (includeSingleton Here) inc : Include scount s} ->
             RA s p -> RA (count scount s {inc}) p
  -- -- -- Introduce
  Unit     : (s : Schema) -> (p : (Place,Place,Place)) -> RA s p

-- union : RA s -> RA s -> RA s
-- union = Union

-- diff: RA s -> RA s' -> RA s
-- diff = Diff

-- (*) : RA s -> RA s' -> RA (s * s')
-- (*) = Product

-- project : (sproj : Schema) -> RA s -> RA (intersect sproj s)
-- project = Project

-- select : (a : Attribute) -> (Expr (getU a) -> Expr BOOL) ->
--          {auto elem : Elem a s} -> RA s -> RA s
-- select = Select

-- drop : (sproj : Schema) -> RA s -> RA (s \\ sproj)
-- drop = Drop

-- count : (scount : Schema) ->
--         {default (includeSingleton Here) inc : Include scount s} ->
--         RA s -> RA (count scount s {inc})
-- count = Count

getSchema : RA s p -> Schema
getSchema _ {s} = s

getPlaces : RA s p -> (Place,Place,Place)
getPlaces _ {p} = p
