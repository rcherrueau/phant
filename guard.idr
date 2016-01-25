module phant.guard

import public utils
import public schema
import public ra

import public crypt

%default total
%access public

||| Type for a Privay Constraint.
|||
||| ````idris example
||| the PC [("Date", NAT), ("Addr", NAT)]
||| ````
PC : Type
PC = List Attribute

using (bctx : Vect n Ctx)

  --------------------------------------------------------- Guard Data Type
  data CState : Type where
    Plain  : Schema -> CState
    FragV  : Vect n Schema -> CState

  data Guard : CState -> CState -> Type -> Type where
    ---- Security combinator
    Encrypt  : (k : String) -> (a : Attribute) ->
               Guard (Plain s)
                     (Plain (encrypt a s))
                     (Expr UNIT bctx)
    EncryptF : (fId : Fin n) -> (k : String) -> (a : Attribute) ->
               Guard (FragV ss)
                     (FragV (encryptF a fId ss))
                     (Expr UNIT bctx)
    Frag     : (sprojs : List Schema) ->
               Guard (Plain s)
                     (FragV (frag sprojs s))
                     (Expr UNIT bctx)
    Query    : (q : RA s bctx -> RA s' bctx) ->
               Guard (Plain s)
                     (Plain s)
                     (Expr (SCH s') bctx)
    QueryF   : (fId : Fin n') ->
               (q : RA (getSchema fId ss) bctx -> RA s' bctx) ->
               Guard (FragV ss)
                     (FragV ss)
                     (Expr (SCH s') bctx)
    Privy    : Guard cs cs' (Expr a bctx -> Expr a bctx)
    ---- Binding for request on expression
    Let      : (ttn : TTName) -> (e : Expr a bctx) ->
               Guard cs cs'
                     (Expr b ((a, process e, ttn) :: bctx)) ->
               Guard cs cs'
                     (Expr b bctx)
    -- ---- Functor
    -- Map      : (m : Expr a bctx -> Expr b bctx) ->
    --            Guard cs cs' bctx (Expr a bctx) ->
    --            Guard cs cs' bctx (Expr b bctx)
    ---- Applicative
    Pure     : Expr a bctx -> Guard cs cs (Expr a bctx)
    SeqApp   : Guard cs cs (Expr a bctx -> Expr b bctx) ->
               Guard cs cs (Expr a bctx) ->
               Guard cs cs (Expr b bctx)
    ---- Monad
    Bind     : Guard cs cs' (Expr a bctx) ->
               (Expr a bctx -> Guard cs' cs'' (Expr b bctx)) ->
               Guard cs cs'' (Expr b bctx)

  ---------------------------------------------------------- Guard Language
  -- map : (m : Expr a bctx -> Expr b bctx) ->
  --       Guard cs cs' bctx (Expr a bctx) ->
  --       Guard cs cs' bctx (Expr b bctx)
  -- map = Map

  pure : Expr a bctx -> Guard cs cs (Expr a bctx)
  pure = Pure

  (<*>) : Guard cs cs (Expr a bctx -> Expr b bctx) ->
          Guard cs cs (Expr a bctx) ->
          Guard cs cs (Expr b bctx)
  (<*>) = SeqApp

  (>>=): Guard cs cs' (Expr a bctx) ->
         (Expr a bctx -> Guard cs' cs'' (Expr b bctx)) ->
         Guard cs cs'' (Expr b bctx)
  (>>=) = Bind

  let_  : (ttn : TTName) -> (e : Expr a bctx) ->
          Guard cs cs'
                (Expr b ((a, process e, ttn) :: bctx)) ->
          Guard cs cs'
                (Expr b bctx)
  let_ ttn = Let ttn

  var_ : HasType bctx i (u,p,tn) -> Expr u bctx
  var_ prf {p} {tn} = ExprLetVar prf tn p

  syntax GUARD [x] "~>" [y] "->" [z] = {bctx : Vect n Ctx} -> Guard x y (Expr z bctx)
  syntax GUARD [x] "->" [z] = GUARD x ~> x -> z
  syntax FRAG [x] = (FragV x)
  syntax DB [x] = (Plain x)

  dsl guard
    let = let_
    variable = var_
    index_first = Stop
    index_next = Pop

  ---------------------------------------------------------- Guard utils
  instance Show (Guard cs cs' e) where
    show (Encrypt k a) =
      "Encrypt " ++ show k ++ " " ++ show a
    show (EncryptF fId k a) =
      "EncryptF" ++ show (finToNat fId) ++ " " ++ show k ++ " " ++ show a
    show (Frag sprojs) =
      "Frag " ++ show sprojs
    show (Query q) = "Query"
    show (QueryF fId q) = "QueryF "
    show Privy = "Privy "
    show (Let ttn e x) = "Let " ++ mkId ttn ++ " " ++ show e ++ show x
    show (Pure x) = "Pure " ++ show x
    show (SeqApp x y) = "SeqApp " ++ show x ++ " " ++ show y
    show (Bind x f) = "Bind " ++ show x

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
