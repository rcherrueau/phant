module phant.guard

import public utils
import public schema
import public crypt

import Data.List
import Data.Vect

%default total
%access public


Ctx : Type
Ctx = (U, TTName, Process)

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
    QVal     : (el u) -> Process -> Query u bctx
    QVar     : HasType bctx i (u,_,_) -> Query u bctx
    QVar_    : TTName -> (u : U) -> Process -> Query u bctx
    QPrivy   : Query u bctx -> Query u bctx
    -- OP/2
    QEq      : Eq (el u) =>
               Query u bctx -> Query u bctx -> Query BOOL bctx
    QElem    : Eq (el u) =>
               Query u bctx -> Query (SCH s) bctx -> Query BOOL bctx
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

  defaultQVal : (u : U) -> Process -> (bctx : Vect n Ctx) -> Query u bctx
  defaultQVal u ppp bctx = QVal (defaultElu u) ppp {bctx}

  getProcess : Query u bctx -> Process
  getProcess (QVal _ ppp)  = ppp
  getProcess (QVar prf)    = getProcess' prf
    where
    getProcess' : HasType bctx' i ctx -> Process
    getProcess' Stop    {bctx' = ((_,_,ppp) :: xs)} = ppp
    getProcess' (Pop y) {bctx' = (x :: xs)}         = getProcess' y {bctx'=xs}
  getProcess (QPrivy x)    = AliceP
  getProcess _             = AppP

  getU : Query u _ -> U
  getU _ {u} = u

  -- getProcess (QEq x y)                  = manageRecipient (getProcess x) (getProcess y)
  -- getProcess (QElem x y)                = manageRecipient (getProcess x) (getProcess y)
  -- getProcess (QProject _ x)             = getProcess x
  -- getProcess (QProduct x y)             = manageRecipient (getProcess x) (getProcess y)
  -- TODO: find how to make QSelect total
  -- getProcess (QSelect (_,u) p x) {bctx} =
  --   -- -- getProcess is only used by Let, so giving AppP to attr is OK
  --   -- let attr = defaultQVal u AppP bctx
  --   --     y    = p attr
  --   -- in manageRecipient (getProcess x) (getProcess y)
  --   getProcess x
  -- getProcess (QCount _ x)               = getProcess x

  -- TODO: set the visibility to private. I can also avoid this with a
  -- special Query constructor.
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
                 Guard cs cs ((a,ttn,getProcess e) :: bctx) (Query b ((a,ttn,getProcess e) :: bctx)) ->
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

  -- let_  : (ttn : TTName) -> (e : Query a bctx) ->
  --         Guard cs cs ((a,ttn,getProcess e) :: bctx) (Query b ((a,ttn,getProcess e) :: bctx)) ->
  --         Guard cs cs bctx (Query b bctx)
  -- let_ ttn = Let ttn

  var_ : HasType bctx i (u,ttn,ppp) -> Query u bctx
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
    let = Let
    variable = var_
    index_first = Stop
    index_next = Pop

  -- ---------------------------------------------------------- Guard utils
  instance Show TTName where
    show x = mkId x

  partial
  printQ : Query u bctx -> String
  printQ (QVal elu ppp) {u = UNIT} =
    "(QVal " ++ show elu ++ "@" ++ show ppp ++ ")"
  printQ (QVal elu ppp) {u = NAT} =
    "(QVal " ++ show elu ++ "@" ++ show ppp ++ ")"
  printQ (QVal elu ppp) {u = TEXT} =
    "(QVal " ++ show elu ++ "@" ++ show ppp ++ ")"
  printQ (QVal elu ppp) {u = REAL} =
    "(QVal " ++ show elu ++ "@" ++ show ppp ++ ")"
  printQ (QVal elu ppp) {u = BOOL} =
    "(QVal " ++ show elu ++ "@" ++ show ppp ++ ")"
  printQ (QVal elu ppp) {u = (CRYPT x)} =
    "(QVal (CRYPT " ++ show x ++ ")@" ++ show ppp ++ ")"
  printQ (QVal elu ppp) {u = (SCH xs)} =
    "(QVal (SCH " ++ show xs ++ ")@" ++ show ppp ++ ")"
  printQ (QVar_ ttn u ppp) =
    -- assert_total $
    "(QVar_ " ++ show ttn ++ ":" ++ show u ++ "@" ++ show ppp ++ ")"
  printQ (QVar prf) = "(QVar " ++ printQ' prf ++ ")"
    where
    partial printQ' : HasType bctx' i ctx -> String
    printQ' Stop    {bctx' = ((ttn,u,ppp) :: xs)} =
      -- assert_total $
      "Z " ++ show ttn ++ ":" ++ show u ++ "@" ++ show ppp
    printQ' (Pop y) {bctx' = (x :: xs)}           =
      "S" ++ printQ' y {bctx'=xs}
  printQ (QPrivy q) =
    "(QPrivy " ++  printQ q ++ ")"
  printQ (QEq q1 q2) =
    "(QEq " ++ printQ q1 ++ " " ++ printQ q2 ++ ")"
  printQ (QElem q1 q2) =
    "(QElem " ++ printQ q1 ++ " " ++ printQ q2 ++ ")"
  printQ (QProject sproj q) =
    "(QProject " ++ show sproj ++ " " ++ printQ q ++ ")"
  printQ (QCount scount q) =
    "(QCount " ++ show scount ++ " " ++ printQ q ++ ")"
  printQ (QProduct q1 q2) =
    "(QProduct " ++ printQ q1 ++ " " ++ printQ q2 ++ ")"
  printQ (QSelect a p q) =
    "(QSelect " ++ show a ++ " " ++ printQ q ++ ")"

  instance Show (Query u bctx) where
    show q = printQ q
    -- show (QVal elu ppp) =
    --   "(QVal " ++ show elu ++ "@" ++ show ppp ++ ")"
    -- show (QVar prf )  = ?mlkj_thd_2
    -- show (QVar_ n' u x) = ?mlkj_thd_3
    -- show (QPrivy x) = ?mlkj_thd_4
    -- show (QEq x y) = ?mlkj_thd_5
    -- show (QElem x y) = ?mlkj_thd_6
    -- show (QProject sproj x) = ?mlkj_thd_7
    -- show (QSelect a p x) = ?mlkj_thd_8
    -- show (QCount scount x) = ?mlkj_thd_9
    -- show (QProduct x y) = ?mlkj_thd_10

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
