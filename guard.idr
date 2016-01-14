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

data CEnv : CState -> Type where
  MkPEnv : (s : Schema) -> CEnv (Plain s)
  MkFEnv : (sprojs : List Schema) -> CEnv $ FragV (frag sproj s)

data Guard : Effect where
  -- Protect : (s : Schema) -> (pcs : List PC) ->
  -- Protect : (pcs : List PC) ->
  --           Guard ()
  --                 (r)
  --                 (\_ => r)
  Encrypt : (k : String) -> (a : Attribute) ->
            Guard ()
                  (CEnv $ Plain s)
                  (\_ => CEnv $ Plain (encrypt a s))
  EncryptF: (fId : Fin n) -> (k : String) -> (a : Attribute) ->
            Guard ()
                  (CEnv $ FragV ss)
                  (\_ => CEnv $ FragV (encryptF a fId ss))
  Frag    : (sprojs : List Schema) ->
            Guard ()
                  (CEnv $ Plain s')
                  (\_ => CEnv $ FragV (frag sprojs s))
  Query   : (q : RA s p -> RA s' p) ->
            Guard (Expr (SCH s') p)
                  (CEnv $ Plain s)
                  (\_ => CEnv $ Plain s)
  QueryF  : (fId : Fin n) ->
            (RA (getSchema fId ss) p -> RA s' p) ->
            Guard (Expr (SCH s') p)
                  (CEnv $ FragV ss)
                  (\_ => CEnv $ FragV ss)

GUARD : CState -> EFFECT
GUARD x = MkEff (CEnv x) Guard

-- -- protect : (s : Schema) -> (pcs : List PC) -> Eff () [GUARD $ PCs pcs] [GUARD $ Plain s]
-- -- protect s pcs = call (Protect s pcs)
-- -- protect : (pcs : List PC) -> Eff () [GUARD $ Plain s]
-- -- protect pcs = call (Protect pcs)

private
recipientIs : Place -> Eff (Expr (SCH s) p) [GUARD a] ->
                       Eff (Expr (SCH s) (setRecipient Alice p)) [GUARD a]
recipientIs p y = do expr <- y
                     pure (setRecipient Alice expr)

privy : Eff (Expr (SCH s) p) [GUARD a] ->
        Eff (Expr (SCH s) (setRecipient Alice p)) [GUARD a]
privy = (recipientIs Alice)

namespace plain
  encrypt : String -> (a : Attribute) -> Eff () [GUARD $ Plain s]
                                                [GUARD $ Plain (encrypt a s)]
  encrypt k a = call (Encrypt k a)

  frag : (sprojs : List Schema) -> Eff () [GUARD $ Plain s]
                                          [GUARD $ FragV (frag sprojs s)]
  frag sprojs = call (Frag sprojs)

  query : (RA s (App, App, DB) -> RA s' (App, App, DB)) ->
          Eff (Expr (SCH s') (App,App,DB)) [GUARD $ Plain s]
  query q = call (Query q)


namespace frag
  encrypt : (fId : Fin n) -> String -> (a : Attribute) ->
            Eff () [GUARD $ FragV ss]
                   [GUARD $ FragV (encryptF a fId ss)]
  encrypt fId k a = call (EncryptF fId k a)

  query : (fId : Fin n) ->
          (RA (getSchema fId ss) (App, App, Frag fId) ->
           RA s'                 (App, App, Frag fId)) ->
          Eff (Expr (SCH s') (App,App,Frag fId)) [GUARD $ FragV ss]
  query fId q = call (QueryF fId q)

  queryL : (RA (getSchema (the (Fin 2) FZ) ss)
               (App, App, Frag (the (Fin 2) FZ)) ->
            RA s'
               (App, App, Frag (the (Fin 2) FZ))) ->
            Eff (Expr (SCH s')
                (App, App, Frag (the (Fin 2) FZ))) [GUARD $ FragV ss]
  queryL q = call (QueryF FZ q)

  queryR : (RA (getSchema (the (Fin 2) (FS FZ)) ss)
               (App, App, Frag (the (Fin 2) (FS FZ))) ->
            RA s'
               (App, App, Frag (the (Fin 2) (FS FZ)))) ->
            Eff (Expr (SCH s')
                (App, App, Frag (the (Fin 2) (FS FZ)))) [GUARD $ FragV ss]
  queryR q = call (QueryF (FS FZ) q)

-- -- Local Variables:
-- -- idris-load-packages: ("effects")
-- -- End:
