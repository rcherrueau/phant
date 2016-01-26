module phant.guard

import public utils
import public schema
import public crypt

import Data.List
import Data.Vect

%default total
%access public


Ctx : Type
Ctx = U

data CState : Type where
  Plain  : Schema -> CState
  FragV  : Vect n Schema -> CState

using (n : Nat, a : U, b : U, u : U,
       bctx : Vect n Ctx, bctx' : Vect m Ctx,
       p : Process, p' : Process, p'' : Process,
       s : Schema, s' : Schema, s'': Schema,
       cs : CState, cs' : CState)

  data HasType : Vect n Ctx -> Fin n -> Ctx -> Type where
    Stop : HasType (ctx :: bctx) FZ ctx
    Pop  : HasType bctx i ctx -> HasType (x :: bctx) (FS i) ctx

  data Query : U -> Vect n Ctx -> Type where
    QVal     : (el u) -> Query u bctx
    QVar     : HasType bctx i u -> Query u bctx
    -- OP/2
    QEq      : Eq (el u) =>
               Query u bctx -> Query u bctx -> Query BOOL bctx
    QElem    : Eq (el u) =>
               Query u bctx -> Query (SCH s) bctx -> Query BOOL bctx
    -- QLet     : (ttn : TTName) -> Query a bctx -> Query
    -- SQL/1
    QProject : (sproj : Schema) ->
               Query (SCH s) bctx -> Query (SCH (intersect sproj s)) bctx
    QSelect  : (a : Attribute) ->
               (p : Query (getU a) bctx -> Query BOOL bctx) ->
               {auto elem : Elem a s} ->
               Query (SCH s) bctx -> Query (SCH s) bctx
    QCount   : (scount : Schema) ->
               {default (includeSingleton Here) inc : Include scount s} ->
               Query (SCH s) bctx -> Query (SCH (count scount s {inc})) bctx
    -- SQL/2
    QProduct : Query (SCH s) bctx -> Query (SCH s') bctx ->
               Query (SCH (s * s')) bctx

  deepQ : Query u bctx -> Query u bctx'
  deepQ = really_believe_me

  (*) : Query (SCH s) bctx -> Query (SCH s') bctx -> Query (SCH (s * s')) bctx
  (*) = QProduct

  namespace qLetRS
    (*) : {v : Vect n Ctx} -> {v' : Vect (S n) Ctx} ->
          Query (SCH s) v -> Query (SCH s') v' -> Query (SCH (s * s')) v'
    (*) q1 q2 = QProduct (deepQ q1) q2

  namespace qLetLS
    (*) : {v : Vect (S n) Ctx} -> {v' : Vect n Ctx} ->
          Query (SCH s) v -> Query (SCH s') v' -> Query (SCH (s * s')) v
    (*) q1 q2 = QProduct q1 (deepQ q2)

  namespace qLetRSS
    (*) : {v : Vect n Ctx} -> {v' : Vect (S (S n)) Ctx} ->
          Query (SCH s) v -> Query (SCH s') v' -> Query (SCH (s * s')) v'
    (*) q1 q2 = QProduct (deepQ q1) q2

  namespace qLetLSS
    (*) : {v : Vect (S (S n)) Ctx} -> {v' : Vect n Ctx} ->
          Query (SCH s) v -> Query (SCH s') v' -> Query (SCH (s * s')) v
    (*) q1 q2 = QProduct q1 (deepQ q2)

  --------------------------------------------------------- Guard Data Type
  namespace g
    data Guard : CState -> CState -> Vect n Ctx -> Type -> Type where
      ---- Security combinator
      Encrypt  : (k : String) -> (a : Attribute) ->
                 Guard (Plain s)
                       (Plain (encrypt a s))
                       bctx
                       (Query UNIT bctx)
      EncryptF : (fId : Fin n) -> (k : String) -> (a : Attribute) ->
                 Guard (FragV ss)
                       (FragV (encryptF a fId ss))
                       bctx
                       (Query UNIT bctx)
      Frag     : (sprojs : List Schema) ->
                 Guard (Plain s)
                       (FragV (frag sprojs s))
                       bctx
                       (Query UNIT bctx)
      Query    : (q : Query (SCH s) bctx -> Query (SCH s') bctx) ->
                 Guard (Plain s)
                       (Plain s)
                       bctx
                       (Query (SCH s') bctx)
      QueryF   : (fId : Fin n') ->
                 (q : Query (SCH (getSchema fId ss)) bctx -> Query (SCH s') bctx) ->
                 Guard (FragV ss)
                       (FragV ss)
                         bctx
                       (Query (SCH s') bctx)
      Privy    : Guard cs cs' bctx (Query a bctx -> Query a bctx)
      ---- Binding for request on expression
      Let      : (ttn : TTName) -> (e : Query a bctx) ->
                 Guard cs cs (a :: bctx) (Query b (a :: bctx)) ->
                 Guard cs cs bctx (Query b bctx)
      -- ---- Functor
      -- Map      : (m : Query a bctx -> Query b bctx) ->
      --            Guard cs cs' bctx (Query a bctx) ->
      --            Guard cs cs' bctx (Query b bctx)
      ---- Applicative
      Pure     : Query a bctx -> Guard cs cs bctx (Query a bctx)
      SeqApp   : Guard cs cs bctx (Query a bctx -> Query b bctx) ->
                 Guard cs cs bctx (Query a bctx) ->
                 Guard cs cs bctx (Query b bctx)
      ---- Monad
      Bind     : Guard cs cs' bctx (Query a bctx) ->
                (Query a bctx -> Guard cs' cs'' bctx (Query b bctx)) ->
                Guard cs cs'' bctx (Query b bctx)

    ---------------------------------------------------------- Guard Language
  -- map : (m : Query a bctx -> Query b bctx) ->
  --       Guard cs cs' bctx (Query a bctx) ->
  --       Guard cs cs' bctx (Query b bctx)
  -- map = Map

  pure : Query a bctx -> Guard cs cs bctx (Query a bctx)
  pure = Pure

  (<*>) : Guard cs cs bctx (Query a bctx -> Query b bctx) ->
          Guard cs cs bctx (Query a bctx) ->
          Guard cs cs bctx (Query b bctx)
  (<*>) = SeqApp

  (>>=): Guard cs cs' bctx (Query a bctx) ->
         (Query a bctx -> Guard cs' cs'' bctx (Query b bctx)) ->
         Guard cs cs'' bctx (Query b bctx)
  (>>=) = Bind

  let_  : (ttn : TTName) -> (e : Query a bctx) ->
          Guard cs cs (a :: bctx) (Query b (a :: bctx)) ->
          Guard cs cs bctx (Query b bctx)
  let_ ttn = Let ttn

  var_ : HasType bctx i u -> Query u bctx
  var_ prf = QVar prf

  data PrinterBctx : Vect n Ctx -> Type where
    MkPB : (bctx : Vect n Ctx) -> PrinterBctx bctx

  printBctx : Query u bctx -> PrinterBctx bctx
  printBctx _ {bctx} = MkPB bctx

  getBctx : Query u bctx -> Vect n Ctx
  getBctx _ {bctx} = bctx

  syntax GUARD [x] "~>" [y] "->" [u] = {bctx : Vect n Ctx} -> Guard x y bctx (Query u bctx)
  syntax GUARD [x] "->" [u] = GUARD x ~> x -> u
  syntax FRAG [x] = (FragV x)
  syntax DB [x] = (Plain x)

  dsl guard
    let = let_
    variable = var_
    index_first = Stop
    index_next = Pop

  -- ---------------------------------------------------------- Guard utils
  -- instance Show (Guard cs cs' e) where
  --   show (Encrypt k a) =
  --     "Encrypt " ++ show k ++ " " ++ show a
  --   show (EncryptF fId k a) =
  --     "EncryptF" ++ show (finToNat fId) ++ " " ++ show k ++ " " ++ show a
  --   show (Frag sprojs) =
  --     "Frag " ++ show sprojs
  --   show (Query q) = "Query"
  --   show (QueryF fId q) = "QueryF "
  --   show Privy = "Privy "
  --   show (Let ttn e x) = "Let " ++ mkId ttn ++ " " ++ show e ++ show x
  --   show (Pure x) = "Pure " ++ show x
  --   show (SeqApp x y) = "SeqApp " ++ show x ++ " " ++ show y
  --   show (Bind x f) = "Bind " ++ show x
