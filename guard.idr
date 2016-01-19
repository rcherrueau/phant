module phant.guard

import public utils
import public schema
import public ra

import public crypt

import public Effects
import Data.List
import public Data.Vect

%default total
%access public

||| Type for a Privay Constraint.
|||
||| ````idris example
||| the PC [("Date", NAT), ("Addr", NAT)]
||| ````
PC : Type
PC = List Attribute

-- Cloud state : plain or frag
data CState : Type where
  Plain  : Schema -> CState
  FragV  : Vect n Schema -> CState

using (bjn : Vect n (U,Process), bjn' : Vect m (U,Process))

  data Guard : CState -> CState -> (bjn : Vect n (U,Process)) -> Type -> Type where
    Encrypt : (k : String) -> (a : Attribute) ->
              Guard (Plain s)
                    (Plain (encrypt a s))
                    bjn
                    (Expr UNIT bjn)
    EncryptF : (fId : Fin n) -> (k : String) -> (a : Attribute) ->
               Guard (FragV ss)
                     (FragV (encryptF a fId ss))
                     bjn
                     (Expr UNIT bjn)
    Frag : (sprojs : List Schema) ->
           Guard (Plain s)
                 (FragV (frag sprojs s))
                        bjn
                 (Expr UNIT bjn)
    Query : (q : RA s bjn -> RA s' bjn) ->
            Guard (Plain s)
                  (Plain s)
                         bjn
                  (Expr (SCH s') bjn)
    QueryF : (fId : Fin n') ->
             (q : RA (getSchema fId ss) bjn -> RA s' bjn) ->
             Guard (FragV ss)
                   (FragV ss)
                          bjn
                   (Expr (SCH s') bjn)
    Privy : Guard cs cs' bjn (Expr a bjn -> Expr a bjn)
    Let  : (e : Expr a bjn) ->
           Guard cs cs' ((a, (getProcess e)) :: bjn) (Expr b ((a, (getProcess e)) :: bjn)) ->
           Guard cs cs' bjn (Expr b bjn)
    -- Functor
    -- Map : (m : Expr a -> Expr b) -> Guard cs cs' bjn (Expr a) -> Guard cs cs' bjn (Expr b)
    -- Applicative
    Pure : Expr a bjn -> Guard cs cs' bjn (Expr a bjn)
    SeqApp : Guard cs cs' bjn (Expr a bjn -> Expr b bjn) -> Guard cs cs' bjn (Expr a bjn) ->
             Guard cs cs' bjn (Expr b bjn)
    -- Monad
    Bind : Guard cs cs' bjn (Expr u bjn) ->
           (Expr u bjn -> Guard cs' cs'' bjn (Expr u' bjn)) -> Guard cs cs'' bjn (Expr u' bjn)

  -- map : (m : Expr a -> Expr b) -> Guard cs cs' bjn (Expr a) -> Guard cs cs' bjn (Expr b)
  -- map = Map

  pure : Expr a bjn -> Guard cs cs' bjn (Expr a bjn)
  pure = Pure

  (<*>) : Guard cs cs' bjn (Expr a bjn -> Expr b bjn) -> Guard cs cs' bjn (Expr a bjn) ->
          Guard cs cs' bjn (Expr b bjn)
  (<*>) = SeqApp

  (>>=) : Guard cs cs' bjn (Expr u bjn) ->
         (Expr u bjn -> Guard cs' cs'' bjn (Expr u' bjn)) -> Guard cs cs'' bjn (Expr u' bjn)
  (>>=) = Bind

  -- let_ : TTName -> Expr u -> Guard cs cs' t -> Guard cs cs' t
  -- let_ n e g = Let (MkVar "n" e)  (\e => g)
  let_  : _ -> (e : Expr a bjn) ->
               Guard cs cs' ((a, (getProcess e)) :: bjn) (Expr b ((a, (getProcess e)) :: bjn)) ->
               Guard cs cs' bjn (Expr b bjn)
  let_ _ = Let

  -- -- Takes an exp of u and make it a variable
  -- var : (bjn : Vect n (U,Process)) -> HasType bjn i a -> Expr a
  -- var (a :: xs) Stop = ExprVar a
  -- var (a :: xs) (Pop x) = var xs x
  var : HasType bjn i (u,p) -> Expr u bjn
  var prf {p} = ExprVar prf p

dsl guard
    let = let_
--     -- C'est quoi qui est le \ids dans la lambda
--     -- Chez moi c'est un ExprVar
    variable = var
    index_first = Stop
    index_next = Pop

-- inter : Guard cs cs' e -> IO c
-- inter (Encrypt k a) = ?inter_rhs_1
-- inter (EncryptF fId k a) = ?inter_rhs_2
-- inter (Frag sprojs) = ?inter_rhs_3
-- inter (Query q) = ?inter_rhs_4
-- inter (QueryF fId q) = ?inter_rhs_5
-- inter Privy = ?inter_rhs_6
-- inter (Let x f) = ?inter_rhs_7
-- inter (Map m x) = ?inter_rhs_8
-- inter (Pure x) = ?inter_rhs_9
-- inter (SeqApp x y) = ?inter_rhs_10
-- inter (Bind x f) = do e <- inter x
--                       inter (f (ExprVar (MkVar "a" e)))


-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
