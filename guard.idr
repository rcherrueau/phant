module phant.guard

import public utils
import public schema
import public ra

import public crypt

import public Effects
import Data.List

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
  FragV  : Schema -> Schema -> CState

data CEnv : CState -> Type where
  MkPEnv : (s : Schema) -> CEnv (Plain s)
  MkFEnv : (sproj : Schema) -> CEnv $ (uncurry FragV) (frag sproj s)

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
  Frag    : (sproj : Schema) ->
            Guard ()
                  (CEnv $ Plain s')
                  (\_ => CEnv $ (uncurry FragV) (frag sproj s))
  Query   : (q : RA s s -> RA s' x) ->
            Guard (Expr (SCH s') x)
                  (CEnv $ Plain s)
                  (\_ => CEnv $ Plain s)
  QueryL  : (q : RA sl sl -> RA sl' x) ->
            Guard (Expr (SCH sl') x)
                  (CEnv $ FragV sl sr)
                  (\_ => CEnv $ FragV sl sr)
  QueryR  : (q : RA sr sr -> RA sr' x) ->
            Guard (Expr (SCH sr') x)
                  (CEnv $ FragV sl sr)
                  (\_ => CEnv $ FragV sl sr)

GUARD : CState -> EFFECT
GUARD x = MkEff (CEnv x) Guard

-- protect : (s : Schema) -> (pcs : List PC) -> Eff () [GUARD $ PCs pcs] [GUARD $ Plain s]
-- protect s pcs = call (Protect s pcs)
-- protect : (pcs : List PC) -> Eff () [GUARD $ Plain s]
-- protect pcs = call (Protect pcs)

encrypt : String -> (a : Attribute) -> Eff () [GUARD $ Plain s]
                                              [GUARD $ Plain (encrypt a s)]
encrypt k a = call (Encrypt k a)

frag : (sproj : Schema) -> Eff () [GUARD $ Plain s]
                                  [GUARD $ (uncurry FragV) (frag sproj s)]
frag sproj = call (Frag sproj)

query : (RA s s -> RA s' x) -> Eff (Expr (SCH s') x) [GUARD $ Plain s]
query q = call (Query q)

queryL : (RA sl sl -> RA sl' x) -> Eff (Expr (SCH sl') x) [GUARD $ FragV sl sr]
queryL q = call (QueryL q)

queryR : (RA sr sr -> RA sr' x) -> Eff (Expr (SCH sr') x) [GUARD $ FragV sl sr]
queryR q = call (QueryR q)

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
