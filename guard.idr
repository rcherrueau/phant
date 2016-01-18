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

DB : Type -> Type
DB = List

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

data Guard : CState -> CState -> Type -> Type where
  Encrypt : (k : String) -> (a : Attribute) ->
            Guard (Plain s)
                  (Plain (encrypt a s))
                  (Expr UNIT)
  EncryptF : (fId : Fin n) -> (k : String) -> (a : Attribute) ->
             Guard (FragV ss)
                   (FragV (encryptF a fId ss))
                   (Expr UNIT)
  Frag : (sprojs : List Schema) ->
         Guard (Plain s)
               (FragV (frag sprojs s))
               (Expr UNIT)
  Query : (q : RA s -> RA s') ->
          Guard (Plain s)
                (Plain s)
                (Expr (SCH s'))
  QueryF : (fId : Fin n) ->
           (q : RA (getSchema fId ss) -> RA s') ->
           Guard (FragV ss)
                 (FragV ss)
                 (Expr (SCH s'))
  Privy : Guard cs cs' (Expr a -> Expr a)
  Let  : TheVar (Expr a) -> (Expr a -> Guard cs cs' (Expr b)) -> Guard cs cs' (Expr b)
  -- Functor
  Map : (m : Expr a -> Expr b) -> Guard cs cs' (Expr a) -> Guard cs cs' (Expr b)
  -- Applicative
  Pure : Expr a -> Guard cs cs' (Expr a)
  SeqApp : Guard cs cs' (Expr a -> Expr b) -> Guard cs cs' (Expr a) -> Guard cs cs' (Expr b)
  -- Monad
  Bind : Guard cs cs' (Expr u) ->
         (Expr u -> Guard cs' cs'' (Expr u')) -> Guard cs cs'' (Expr u')

map : (m : Expr a -> Expr b) -> Guard cs cs' (Expr a) -> Guard cs cs' (Expr b)
map = Map

pure : Expr a -> Guard cs cs' (Expr a)
pure = Pure

(<*>) : Guard cs cs' (Expr a -> Expr b) -> Guard cs cs' (Expr a) -> Guard cs cs' (Expr b)
(<*>) = SeqApp

(>>=) : Guard cs cs' (Expr u) ->
       (Expr u -> Guard cs' cs'' (Expr u')) -> Guard cs cs'' (Expr u')
(>>=) = Bind

-- let_ : TTName -> Expr u -> Guard cs cs' t -> Guard cs cs' t
-- let_ n e g = Let (MkVar "n" e)  (\e => g)

-- -- Takes an exp of u and make it a variable
-- var : Expr u -> Expr u
-- var e = ExprVar (MkVar "a" e)

-- dsl guard
--     -- let = let_
--     -- C'est quoi qui est le \ids dans la lambda
--     -- Chez moi c'est un ExprVar
--     variable = var
--     -- index_first = idxfst
inter : Guard cs cs' e -> IO c
inter (Encrypt k a) = ?inter_rhs_1
inter (EncryptF fId k a) = ?inter_rhs_2
inter (Frag sprojs) = ?inter_rhs_3
inter (Query q) = ?inter_rhs_4
inter (QueryF fId q) = ?inter_rhs_5
inter Privy = ?inter_rhs_6
inter (Let x f) = ?inter_rhs_7
inter (Map m x) = ?inter_rhs_8
inter (Pure x) = ?inter_rhs_9
inter (SeqApp x y) = ?inter_rhs_10
inter (Bind x f) = do e <- inter x
                      inter (f (ExprVar (MkVar "a" e)))

-- -- inter (Encrypt k a) = ?inter_rhs_1
-- -- inter (EncryptF fId k a) = ?inter_rhs_2
-- -- inter (Frag sprojs) = ?inter_rhs_3
-- -- inter (Query q) = ?inter_rhs_4
-- -- inter (QueryF fId q) = ?inter_rhs_5
-- -- inter Privy = ?inter_rhs_6
-- -- inter (Let x k) = ?inter_rhs_7
-- -- inter (Map m g) = ?inter_rhs_8
-- -- inter (Pure e) = ?inter_rhs_9
-- -- inter (SeqApp f g) = ?inter_rhs_10
-- -- inter (Bind g f)     = do e <- (inter g)
-- --                           (inter $ f (ExprVar (MkVar "a" e)))


-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
