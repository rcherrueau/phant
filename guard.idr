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
  Query   : (q : RA s -> RA s') ->
            Guard (Expr (SCH s'))
                  (CEnv $ Plain s)
                  (\_ => CEnv $ Plain s)
  QueryF  : (fId : Fin n) -> (RA (getSchema fId ss) -> RA s') ->
            Guard (Expr (SCH s'))
                  (CEnv $ FragV ss)
                  (\_ => CEnv $ FragV ss)

GUARD : CState -> EFFECT
GUARD x = MkEff (CEnv x) Guard

-- -- protect : (s : Schema) -> (pcs : List PC) -> Eff () [GUARD $ PCs pcs] [GUARD $ Plain s]
-- -- protect s pcs = call (Protect s pcs)
-- -- protect : (pcs : List PC) -> Eff () [GUARD $ Plain s]
-- -- protect pcs = call (Protect pcs)

namespace plain
  encrypt : String -> (a : Attribute) -> Eff () [GUARD $ Plain s]
                                                [GUARD $ Plain (encrypt a s)]
  encrypt k a = call (Encrypt k a)

  frag : (sprojs : List Schema) -> Eff () [GUARD $ Plain s]
                                          [GUARD $ FragV (frag sprojs s)]
  frag sprojs = call (Frag sprojs)

  query : (RA s -> RA s') -> Eff (Expr (SCH s')) [GUARD $ Plain s]
  query q = call (Query q)

namespace frag
  encrypt : (fId : Fin n) -> String -> (a : Attribute) ->
            Eff () [GUARD $ FragV ss]
                   [GUARD $ FragV (encryptF a fId ss)]
  encrypt fId k a = call (EncryptF fId k a)

  query : (fId : Fin n) ->
          (RA (getSchema fId ss) -> RA s') ->
          Eff (Expr (SCH s')) [GUARD $ FragV ss]
  query fId q = call (QueryF fId q)

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
