module phant.guard

import public utils
import public schema
import public table
import public ra

import Effects
import Data.List

%default total
%access public

DB : Type -> Type
DB = List

-- Cloud state : plain or frag
data CState : Type where
  Plain  : Schema -> CState
  FragV  : Schema -> Schema -> CState

data CEnv : CState -> Type where
  MkPEnv : (s : Schema) -> CEnv (Plain s)
  MkFEnv : (sproj : Schema) -> CEnv $ (uncurry FragV) (frag sproj s)

data Guard : Effect where
  Encrypt : (k : String) -> (a : Attribute) ->
            Guard ()
                  (CEnv $ Plain s)
                  (\_ => CEnv $ Plain (encrypt a s))
  Frag    : (sproj : Schema) ->
            Guard ()
                  (CEnv $ Plain s')
                  (\_ => CEnv $ (uncurry FragV) (frag sproj s))
  Query   : (q : RA s -> RA s') ->
            Guard (DB $ liftSch s')
                  (CEnv $ Plain s)
                  (\_ => CEnv $ Plain s)
  QueryL  : (q : RA sl -> RA sl') ->
            Guard (DB $ liftSch sl')
                  (CEnv $ FragV sl sr)
                  (\_ => CEnv $ FragV sl sr)
  QueryR  : (q : RA sr -> RA sr') ->
            Guard (DB $ liftSch sr')
                  (CEnv $ FragV sl sr)
                  (\_ => CEnv $ FragV sl sr)

GUARD : CState -> EFFECT
GUARD x = MkEff (CEnv x) Guard

encrypt : String -> (a : Attribute) -> Eff () [GUARD $ Plain s]
                                              [GUARD $ Plain (encrypt a s)]
encrypt k a = call (Encrypt k a)

frag : (sproj : Schema) -> Eff () [GUARD $ Plain s]
                                  [GUARD $ (uncurry FragV) (frag sproj s)]
frag sproj = call (Frag sproj)

query : (RA s -> RA s') -> Eff (DB $ liftSch s') [GUARD $ Plain s]
query q = call (Query q)

queryL : (RA sl -> RA sl') -> Eff (DB $ liftSch sl') [GUARD $ FragV sl sr]
queryL q = call (QueryL q)

queryR : (RA sr -> RA sr') ->
         Eff (DB $ liftSch sr') [GUARD $ FragV sl sr]
queryR q = call (QueryR q)

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
