module phant.ra

import public schema
import utils
import crypt

import Data.List
import Data.Vect

%default total
%access public

Ctx : Type
Ctx = (U, Process, TTName)

using (bctx : Vect n Ctx, p : Process, p' : Process, p'' : Process)

  data HasType : Vect n Ctx -> Fin n -> Ctx -> Type where
    Stop : HasType (a :: bctx) FZ a
    Pop  : HasType bctx i b -> HasType (a :: bctx) (FS i) b


  data Expr : U -> Vect n Ctx -> Type where
    -- ExprElU : {u : U} -> (v : a) -> Expr u
    -- ExprPAIR  : (Pair (el x) (el y)) -> Expr (PAIR x y)
    -- Type
    -- ExprU     :  (u : U) -> (p : Process) -> Expr u p
    -- ExprUNIT  : Expr UNIT bctx
    -- ExprNAT   : Nat -> Expr NAT bctx
    -- ExprTEXT  : String -> Expr TEXT Nil
    -- ExprREAL  : Double -> Expr REAL bctx
    -- ExprBOOL  : Bool -> Expr BOOL bctx
    -- ExprCRYPT : {u : U} -> AES (el u) -> Expr (CRYPT u) Nil
    -- ExprSCH     : (s : Schema) ->  Expr (SCH s) bctx
    ExprVal   : {default Nil bctx : Vect n Ctx} -> {u : U} -> Process -> (el u) -> Expr u bctx
    -- Operation
    ExprEq    : Eq (el a) => Expr a bctx -> Expr a bjn' -> Expr BOOL bjn''
    -- ExprGtEq  : Ord (el a) => Expr a bctx -> Expr a bctx -> Expr BOOL bctx
    ExprElem  : Eq (el a) => Expr a bctx -> Expr (SCH s) bctx -> Expr BOOL bctx
    -- ExprNot   : Expr BOOL bctx -> Expr BOOL bctx
    -- Schema
    -- ExprUnion   : Expr (SCH s) -> Expr (SCH s) -> Expr (SCH s)
    -- ExprDiff    : Expr (SCH s) -> Expr (SCH s') -> Expr (SCH s)
    ExprProduct : Expr (SCH s) bctx -> Expr (SCH s') bjn' ->
                  Expr (SCH (s * s')) bjn''
    ExprProject : (sproj : Schema) -> Expr (SCH s) bctx -> Expr (SCH (intersect sproj s)) bctx

    -- ExprSelect  : {s : Schema} -> (a : Attribute) -> (Expr (getU a) p -> Expr BOOL p') ->
    --               {auto elem : Elem a s} -> Expr (SCH s) p -> Expr (SCH s) (findRecipient p p')
    -- ExprDrop    : (sproj : Schema) -> Expr (SCH s) -> Expr (SCH (s \\ sproj))
    ExprCount   : (scount : Schema) ->
                  {default (includeSingleton Here) inc : Include scount s} ->
                  Expr (SCH s) bctx -> Expr (SCH (count scount s {inc})) bctx
    ExprPrivy   : Expr a bctx -> Expr a bctx
    ExprVar     : HasType bctx i (u,_) -> TTName -> Process -> Expr u bctx
    ExprVar'    : TTName -> Expr u bctx -> Expr u bctx

  process : Expr u bctx -> Process
  process (ExprVal p elu)   = p
  process (ExprVar prf n p) = p
  process (ExprVar' n e)    = process e
  process (ExprPrivy e)     = AliceP
  process _                 = AppP

-- namespace expr
  -- -- Set the recipient of an expression
  -- setRecipient : (p : Place) -> Expr a ppp -> Expr a (setRecipient p ppp)
  -- setRecipient p expr {ppp} = let ppp' = setRecipient p ppp
  --                             in ExprPutP ppp' expr

  -- defaultExpr : (u : U) -> Expr u
  -- defaultExpr UNIT      = ExprUNIT
  -- defaultExpr NAT       = ExprNAT Z
  -- defaultExpr TEXT      = ExprTEXT ""
  -- defaultExpr REAL      = ExprREAL 0.0
  -- defaultExpr BOOL      = ExprBOOL True
  -- defaultExpr (CRYPT u) = let expr = defaultExpr u
  --                             elu = defaultElu expr
  --                             aes = encrypt "key" elu
  --                          in ExprCRYPT aes
  --   where
  --   defaultElu : Expr u' -> (el u')
  --   defaultElu _               {u' = UNIT      } = ()
  --   defaultElu _               {u' = NAT       } = Z
  --   defaultElu _               {u' = TEXT      } = ""
  --   defaultElu _               {u' = REAL      } = 0.0
  --   defaultElu _               {u' = BOOL      } = True
  --   defaultElu (ExprCRYPT y)   {u' = (CRYPT x) } = y
  --   defaultElu (ExprPutP  y)   {u' = (CRYPT x) } = defaultElu y
  --   defaultElu (ExprVar (MkVar s y))     {u' = (CRYPT x) } = assert_total $ defaultElu y
  --   defaultElu _               {u' = (SCH xs)  } = []
  -- defaultExpr (SCH s)  = ExprSCH s

  -- -- givemeExpr : (u : U) -> (p : Process) -> Expr u p
  -- -- givemeExpr u p = ExprU u p

  -- -- Operation
  -- -- (==) : Eq (el a) => Expr a -> Expr a -> Expr BOOL
  -- -- (==) = ExprEq

  -- -- (>=) : Ord (el a) => Expr a -> Expr a -> Expr BOOL
  -- -- (>=) = ExprGtEq

  -- -- elem : Eq (el a) => Expr a -> Expr (SCH s) -> Expr BOOL
  -- -- elem = ExprElem

  -- -- not : Expr BOOL -> Expr BOOL
  -- -- not = ExprNot

  -- const : Expr a  p1 -> Expr b p2 -> Expr a p1
  -- const a b = a

  -- encrypt : Crypt (el u) (AES (el u)) => Key -> (el u) -> Expr (CRYPT u) AppP
  -- encrypt k x = ExprCRYPT (encrypt k x)
  -- -- encrypt k x {u} = ExprU (CRYPT u) AppP

  -- -- union : Expr $ SCH s -> Expr $ SCH s -> Expr $ SCH s
  -- -- union = ExprUnion

  -- -- diff : Expr $ SCH s -> Expr $ SCH s' -> Expr $ SCH s
  -- -- diff = ExprDiff

  -- -- (*) : Expr $ SCH s -> Expr $ SCH s' -> Expr $ SCH (s * s')
  -- -- (*) = ExprProduct

  -- -- project : (sproj : Schema) -> Expr $ SCH s -> Expr $ SCH (intersect sproj s)
  -- -- project = ExprProject

  -- -- select : {s : Schema} -> (a : Attribute) -> (Expr (getU a) -> Expr BOOL) ->
  -- --        {auto elem : Elem a s} -> Expr $ SCH s -> Expr $ SCH s
  -- -- select = assert_total ExprSelect

  -- -- drop : (sproj : Schema) -> Expr $ SCH s -> Expr $ SCH (s \\ sproj)
  -- -- drop = ExprDrop

  -- -- count : (scount : Schema) ->
  -- --         {default (includeSingleton Here) inc : Include scount s} ->
  -- --         Expr $ SCH s -> Expr $ SCH (count scount s {inc})
  -- -- count = ExprCount
  -- -- -- Implicit conversion for dsl
  -- -- -- -- λΠ> the (Expr (PAIR NAT (PAIR NAT UNIT))) (1,1,())
  -- -- -- implicit pairPAIR : (Pair (el x) (el y)) -> Expr (PAIR x y)
  -- -- -- pairPAIR = ExprPAIR

  -- -- implicit unitUNIT : () -> Expr UNIT
  -- -- unitUNIT _ = ExprUNIT

  -- -- implicit natNAT : Nat -> Expr NAT
  -- -- natNAT = ExprNAT

  -- -- implicit stringTEXT : String -> Expr TEXT
  -- -- stringTEXT = ExprTEXT

  -- -- implicit doubleREAL : Double -> Expr REAL
  -- -- doubleREAL = ExprREAL

  -- -- implicit boolBOOL : Bool -> Expr BOOL
  -- -- boolBOOL = ExprBOOL

  -- -- implicit aesCRYPT : AES (el u) -> Expr (CRYPT u)
  -- -- aesCRYPT = ExprCRYPT

  -- -- implicit schemaSCH : (l : Schema) -> Expr (SCH l)
  -- -- schemaSCH = ExprSCH


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

  data RA : Schema -> Vect n Ctx -> Type where
    -- Set operators
    -- Union    : RA s  -> RA s  -> RA s
    -- Diff     : RA s  -> RA s' -> RA s
    -- Product  : RA s  -> RA s' -> RA (s * s')
    -- Others
    -- Project  : (sproj : Schema) -> RA s -> RA (intersect sproj s)
    -- Dans mon context, j'enleve le s puis je remet le
    Project  : (sproj : Schema) -> RA s bctx -> RA (intersect sproj s) bctx
    -- TODO: Select on an element with specific operation
    Select  : (a : Attribute) ->
              (Expr (getU a) bctx -> Expr BOOL bctx) ->
              {auto elem : Elem a s} -> RA s bctx -> RA s bctx
    -- -- TODO: Join take an element to do the join
    -- Drop     : (sproj : Schema) -> RA s  -> RA (s \\ sproj)
    -- -- FIXME: Do a better tatic, Something that work on each schema
    -- -- rather than schema singleton
    Count    : (scount : Schema) ->
               {default (includeSingleton Here) inc : Include scount s} ->
               RA s bctx -> RA (count scount s {inc}) bctx
    -- -- -- Introduce
    Unit     : (s : Schema) -> RA s bctx

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

  getSchema : RA s bctx -> Schema
  getSchema _ {s} = s

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
