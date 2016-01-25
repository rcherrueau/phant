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

-- biggest : Vect n Ctx -> Vect m Ctx -> Vect (maximum n m) Ctx
-- biggest xs ys {n} {m} with (decEq n m)
--   biggest xs ys {n = n} {m = m} | (Yes prf) = rewrite sym prf in
--                                               rewrite maximumIdempotent n in xs
--   biggest [] ys {n = Z} {m = m} | (No contra) = ys
--   biggest (x :: xs) [] {n = (S k)} {m = Z} | (No contra) = (x :: xs)
--   biggest (x :: xs) (y :: ys) {n = (S k)} {m = (S j)} | (No contra) = let rec = (biggest xs ys)
--                                                                       in x :: rec

maxi_lemma : (maximum (S j) (S k) = S j -> Void) -> maximum j k = j -> Void
maxi_lemma contra prf = void $ contra $ cong prf {f=S}

maximumIsTheOther : (l : Nat) -> (r : Nat) -> ((maximum l r = l) -> Void) -> maximum l r = r
maximumIsTheOther l r contra with (decEq (maximum l r) r)
  maximumIsTheOther l r contra | (Yes prf) = prf
  maximumIsTheOther l     Z     contra | (No f) =
    let maxLZisL = maximumZeroNLeft l
    in void (contra maxLZisL)
  maximumIsTheOther Z     (S k) contra | (No f) =
    Refl
  maximumIsTheOther (S j) (S k) contra | (No f) =
    let nMaxJKisJ = maxi_lemma contra
        maxJKisK  = maximumIsTheOther j k nMaxJKisJ
    in cong maxJKisK {f=S}

biggest : Vect n Ctx -> Vect m Ctx -> Vect (maximum n m) Ctx
biggest xs ys {n = Z} = ys
biggest xs ys {n}     {m = Z} =
        rewrite maximumZeroNLeft n in xs
biggest xs ys {n}     {m} with (decEq n m)
  biggest xs ys {n}     {m} | (Yes prf) =
          rewrite sym prf in
          rewrite maximumIdempotent n in xs
  biggest xs ys {n}     {m} | (No _) with (decEq (maximum n m) n)
    biggest xs ys {n}     {m} | (No _) | (Yes prf) =
            rewrite prf in xs
    biggest xs ys {n}     {m} | (No _) | (No contra) =
            let prf = maximumIsTheOther n m contra
            in rewrite prf in ys
-- biggest xs ys {n} {m} with (decEq (maximum n m) n)
--   biggest xs ys {n} {m} | (Yes prf) = rewrite prf in xs
--   biggest xs ys {n} {m} | (No contra) = let prf = maximumIsTheOther n m contra
--                                         in rewrite prf in ys

using (bctx : Vect n Ctx, -- bctx' : Vect m Ctx, bctx'' : Vect l Ctx,
       p : Process, p' : Process, p'' : Process,
       s : Schema, s' : Schema)

  data HasType : Vect n Ctx -> Fin n -> Ctx -> Type where
    Stop : HasType (a :: bctx) FZ a
    Pop  : HasType bctx i b -> HasType (a :: bctx) (FS i) b

  -- downHasCtx : HasType (x :: bctx) (FS i) ctx  -> HasType bctx i ctx
  -- downHasCtx (Pop x) = x

  data Expr : U -> Vect n Ctx -> Type where
    -- Operation
    ExprEq    : Eq (el a) =>
                -- {default Nil bctx : Vect n Ctx} -> {default Nil bctx' : Vect m Ctx} ->
                Expr a bctx' -> Expr a bctx -> Expr BOOL bctx
    -- ExprGtEq  : Ord (el a) => Expr a bctx -> Expr a bctx -> Expr BOOL bctx
    ExprElem  : Eq (el a) => Expr a bctx -> Expr (SCH s) bctx -> Expr BOOL bctx
    -- ExprNot   : Expr BOOL bctx -> Expr BOOL bctx
    -- Schema
    -- ExprUnion   : Expr (SCH s) -> Expr (SCH s) -> Expr (SCH s)
    -- ExprDiff    : Expr (SCH s) -> Expr (SCH s') -> Expr (SCH s)
    ExprProduct : -- {default Nil bctx : Vect n Ctx} -> {default Nil bctx' : Vect m Ctx} ->
                  Expr (SCH s) bctx' -> Expr (SCH s') bctx ->
                  -- Expr (SCH (s * s')) (biggest bctx bctx')
                  Expr (SCH (s * s')) bctx
    ExprProject : (sproj : Schema) -> Expr (SCH s) bctx -> Expr (SCH (intersect sproj s)) bctx

    -- ExprSelect  : {s : Schema} -> (a : Attribute) -> (Expr (getU a) p -> Expr BOOL p') ->
    --               {auto elem : Elem a s} -> Expr (SCH s) p -> Expr (SCH s) (findRecipient p p')
    -- ExprDrop    : (sproj : Schema) -> Expr (SCH s) -> Expr (SCH (s \\ sproj))
    ExprCount   : (scount : Schema) ->
                  {default (includeSingleton Here) inc : Include scount s} ->
                  Expr (SCH s) bctx -> Expr (SCH (count scount s {inc})) bctx
    ExprPrivy   : Expr a bctx -> Expr a bctx
    ExprVal   : {default Nil bctx : Vect n Ctx} -> {u : U} ->
                 Process -> (el u) -> Expr u bctx
    ExprLetVar : HasType bctx i (u,p,ttn) -> TTName -> Process -> Expr u bctx
    ExprVar    : TTName -> Expr u bctx -> Expr u bctx

  -- -- il ne peux pas reduire car n'infère pas de taille pour le `n` de
  -- -- `bctx`
  -- lala : {default (%runElab ?mlkj) v : Vect n Ctx} -> Expr TEXT bctx -> Expr BOOL v
  -- -- lala : Expr TEXT bctx -> Expr BOOL bctx
  -- lala e = ExprEq e (ExprVal AppP "lala")

  (==) : Eq (el a) => Expr a bctx' -> Expr a bctx -> Expr BOOL bctx
  (==) = ExprEq

  (*) : Expr (SCH s) bctx' -> Expr (SCH s') bctx -> Expr (SCH (s * s')) bctx
  (*) = ExprProduct


  process : Expr u bctx -> Process
  process (ExprVal p elu)   = p
  process (ExprLetVar prf n p) = p
  process (ExprVar n e)    = process e
  process (ExprPrivy e)     = AliceP
  process _                 = AppP

  ||| Produces an ExprVal for a specific type of the universse U.
  defaultExprVal : (u : U) -> (bctx : Vect n Ctx) -> Process -> Expr u bctx
  defaultExprVal u bctx ppp = ExprVal {bctx} {u} ppp (defaultElu u)

  mkId : TTName -> String
  mkId (UN x) = x
  mkId (NS n xs) = let name = mkId n
                       nspace = concat (intersperse "." (reverse xs))
                   in nspace ++ "." ++ name
  mkId (MN x y) = y ++ show x
  mkId (SN x) = "special_name"

  instance Show (Expr u bctx) where
    show (ExprVal ppp elu) {u = UNIT} =
      "(Val " ++ show elu ++ "@" ++ show ppp ++ ")"
    show (ExprVal ppp elu) {u = NAT} =
      "(Val " ++ show elu ++ "@" ++ show ppp ++ ")"
    show (ExprVal ppp elu) {u = TEXT} =
      "(Val " ++ show elu ++ "@" ++ show ppp ++ ")"
    show (ExprVal ppp elu) {u = REAL} =
      "(Val " ++ show elu ++ "@" ++ show ppp ++ ")"
    show (ExprVal ppp elu) {u = BOOL} =
      "(Val " ++ show elu ++ "@" ++ show ppp ++ ")"
    show (ExprVal ppp elu) {u = (CRYPT x)} =
      "(Val CRYPT " ++ show x ++ "@" ++ show ppp ++ ")"
    show (ExprVal ppp elu) {u = (SCH xs)} =
      "(Val SCH " ++ show xs ++ "@" ++ show ppp ++ ")"
    show (ExprEq x y) = show x ++ " == " ++ show y
    show (ExprElem x y) = show x ++ " elem " ++ show y
    show (ExprProduct x y) = show x ++ " * " ++ show y
    show (ExprProject sproj x) = "project " ++ show sproj ++ " " ++ show x
    show (ExprCount scount x) = "count " ++ show scount ++ " " ++ show x
    show (ExprPrivy x) = "privy " ++ show x
    show (ExprLetVar prf ttn ppp) = "(LetVar " ++ mkId ttn ++ "@" ++ show ppp ++ ")"
    show (ExprVar ttn e) = "(Var "++ mkId ttn ++ show e ++ ")"

    -- dropBctx : Expr u bctx -> Expr u []

  -- downBctx : Expr u (x :: bctx) -> Expr u bctx
  -- downBctx (ExprVal ppp elu) {bctx} = ExprVal ppp elu {bctx}
  -- downBctx (ExprVar Stop ttn ppp)  = ?ljm_1 -- TODO: Make it absurd
  -- downBctx (ExprVar (Pop prf) ttn ppp) {bctx} = ExprVar prf ttn ppp
  -- downBctx (ExprVar' n x) = ?downBctx_rhs_9
  -- downBctx (ExprEq x y) = ?downBctx_rhs_2
  -- downBctx (ExprElem x y) = ?downBctx_rhs_3
  -- downBctx (ExprProduct x y) = ?downBctx_rhs_4
  -- downBctx (ExprProject sproj x) = ?downBctx_rhs_5
  -- downBctx (ExprCount scount x) = ?downBctx_rhs_6
  -- downBctx (ExprPrivy x) = ?downBctx_rhs_7

-- namespace expr
  -- -- Set the recipient of an expression
  -- setRecipient : (p : Place) -> Expr a ppp -> Expr a (setRecipient p ppp) bb
  -- setRecipient p expr {ppp} = let ppp' = setRecipient p ppp
  --                             in ExprPutP ppp' expr


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
    Select  :  -- {default Nil bctx : Vect n Ctx} ->
              (a : Attribute) ->
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

  instance Show (RA s bctx) where
    show (Project sproj x) = "project " ++ show sproj ++ " " ++ show x
    show (Select a f x) = "select " ++ show a ++ " "  ++  show x
    show (Count scount x) = "count " ++ show scount ++ " " ++ show x
    show (Unit s) = "unit " ++ show s

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
