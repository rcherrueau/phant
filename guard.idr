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


using (n : Nat, a : U, b : U, u : U,
       bctx : Vect n Ctx, bctx' : Vect m Ctx, bctx'' : Vect l Ctx,
       p : Process, p' : Process, p'' : Process,
       s : Schema, s' : Schema, s'': Schema)

  --------------------------------------------------------- Guard Data Type
  data CState : Type where
    Plain  : Schema -> CState
    FragV  : Vect n Schema -> CState

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
    Query    : (q : Query (SCH s) bctx -> Query (SCH s') bctx') ->
               Guard (Plain s)
                     (Plain s)
                     bctx
                     (Query (SCH s') bctx')
    QueryF   : (fId : Fin n') ->
               (q : Query (SCH (getSchema fId ss)) bctx -> Query (SCH s') bctx') ->
               Guard (FragV ss)
                     (FragV ss)
                       bctx
                     (Query (SCH s') bctx')
    Privy    : Guard cs cs' bctx (Query a bctx -> Query a bctx)
    ---- Binding for request on expression
    Let      : (ttn : TTName) -> (e : Query a bctx') ->
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
  pure q {bctx} {cs} {a} = believe_me (Pure q {bctx} {cs} {a})

  (<*>) : Guard cs cs bctx (Query a bctx -> Query b bctx) ->
          Guard cs cs bctx (Query a bctx) ->
          Guard cs cs bctx (Query b bctx)
  (<*>) = SeqApp

  (>>=): Guard cs cs' bctx (Query a bctx) ->
         (Query a bctx -> Guard cs' cs'' bctx (Query b bctx)) ->
         Guard cs cs'' bctx (Query b bctx)
  (>>=) = Bind

  let_  : (ttn : TTName) -> (e : Query a bctx') ->
          Guard cs cs (a :: bctx) (Query b (a :: bctx)) ->
          Guard cs cs bctx (Query b bctx)
  let_ ttn = Let ttn

  var_ : HasType bctx i u -> Query u bctx
  -- var_ prf = QVar prf
  var_ Stop    {bctx = (u :: xs)} = believe_me $ QVar (Stop {ctx=u} {bctx=xs})
  var_ (Pop y) {bctx = (x :: xs)} = QVar (Pop y {x} {bctx=xs})


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
