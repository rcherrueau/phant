module phant.ra

import public schema
import utils
import crypt

import Data.List
import Debug.Trace
import Data.Vect

%default total
%access public

data Place : Type where
     Alice : Place
     App   : Place
     DB    : Place
     Frag  : Fin n -> Place

Process : Type
Process = (Place,Place,Place)

instance Eq Place where
  Alice    == Alice    = True
  App      == App      = True
  DB       == DB       = True
  (Frag j) == (Frag k) = finToNat j == finToNat k
  _        == _        = False

caller : Process -> Place
caller = fst . snd

callee : Process -> Place
callee = snd . snd

recipient : Process -> Place
recipient = fst

setRecipient : Place -> Process -> Process
setRecipient r (a, b, c) = (r , b, c)

AppP : Process
AppP = (App, App, App)

AliceP : Process
AliceP = (Alice, Alice, Alice)

findRecipient : Process -> Process -> Process
findRecipient (recip1, _, _) (recip2, _, _) =
  if recip1 == Alice || recip2 == Alice
  -- It should not be something different since I cannot do Exp*
  -- computation on other place rather than Alice and App.
  then (Alice,Alice,Alice) else (App,App,App)


using (bjn : Vect n U, bjn' : Vect m U)

  data HasType : Vect n U -> Fin n -> U -> Type where
    Stop : HasType (a :: bjn) FZ a
    Pop  : HasType bjn i b -> HasType (a :: bjn) (FS i) b


  data Expr : U -> Vect n U -> Type where
    -- ExprElU : {u : U} -> (v : a) -> Expr u
    -- ExprPAIR  : (Pair (el x) (el y)) -> Expr (PAIR x y)
    -- Type
    -- ExprU     :  (u : U) -> (p : Process) -> Expr u p
    ExprUNIT  : Expr UNIT bjn
    ExprNAT   : Nat -> Expr NAT bjn
    ExprTEXT  : String -> Expr TEXT bjn
    ExprREAL  : Double -> Expr REAL bjn
    ExprBOOL  : Bool -> Expr BOOL bjn
    ExprCRYPT : {u : U} -> AES (el u) -> Expr (CRYPT u) bjn
    ExprSCH     : (s : Schema) ->  Expr (SCH s) bjn
    -- Operation
    -- ExprEq    : Eq (el a) => Expr a bjn -> Expr a bjn -> Expr BOOL bjn
    -- ExprGtEq  : Ord (el a) => Expr a bjn -> Expr a bjn -> Expr BOOL bjn
    ExprElem  : Eq (el a) => Expr a bjn -> Expr (SCH s) bjn -> Expr BOOL bjn
    -- ExprNot   : Expr BOOL bjn -> Expr BOOL bjn
    -- Schema
    -- ExprUnion   : Expr (SCH s) -> Expr (SCH s) -> Expr (SCH s)
    -- ExprDiff    : Expr (SCH s) -> Expr (SCH s') -> Expr (SCH s)
    ExprProduct : Expr (SCH s) bjn -> Expr (SCH s') bjn ->
                  Expr (SCH (s * s')) bjn
    ExprProject : (sproj : Schema) -> Expr (SCH s) bjn -> Expr (SCH (intersect sproj s)) bjn

    -- ExprSelect  : {s : Schema} -> (a : Attribute) -> (Expr (getU a) p -> Expr BOOL p') ->
    --               {auto elem : Elem a s} -> Expr (SCH s) p -> Expr (SCH s) (findRecipient p p')
    -- ExprDrop    : (sproj : Schema) -> Expr (SCH s) -> Expr (SCH (s \\ sproj))
    -- ExprCount   : (scount : Schema) ->
    --               {default (includeSingleton Here) inc : Include scount s} ->
    --               Expr (SCH s) -> Expr (SCH (count scount s {inc}))
    -- ExprPutP    : Expr a -> Expr a
    ExprVar     : HasType bjn i a -> Expr t bjn


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

  data RA : Schema -> Vect n U -> Type where
    -- Set operators
    -- Union    : RA s  -> RA s  -> RA s
    -- Diff     : RA s  -> RA s' -> RA s
    -- Product  : RA s  -> RA s' -> RA (s * s')
    -- Others
    -- Project  : (sproj : Schema) -> RA s -> RA (intersect sproj s)
    -- Dans mon context, j'enleve le s puis je remet le
    Project  : (sproj : Schema) -> RA s bjn -> RA (intersect sproj s) bjn
    -- TODO: Select on an element with specific operation
    Select  : (a : Attribute) ->
              (Expr (getU a) bjn -> Expr BOOL bjn) ->
              {auto elem : Elem a s} -> RA s bjn -> RA s bjn
    -- -- TODO: Join take an element to do the join
    -- Drop     : (sproj : Schema) -> RA s  -> RA (s \\ sproj)
    -- -- FIXME: Do a better tatic, Something that work on each schema
    -- -- rather than schema singleton
    Count    : (scount : Schema) ->
               {default (includeSingleton Here) inc : Include scount s} ->
               RA s bjn -> RA (count scount s {inc}) bjn
    -- -- -- Introduce
    Unit     : (s : Schema) -> RA s bjn

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

  getSchema : RA s bjn -> Schema
  getSchema _ {s} = s

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
