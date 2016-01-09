module phant.guard

import public utils
import public schema
import public table
import public ra

import Effects
import Data.List

%default total
%access public

fragWIp : (sproj : Schema) -> (s : Schema) ->
          (ipl: String) -> (ipr : String) -> (Loc ipl Schema, Loc ipr Schema)
fragWIp sproj s ipl ipr = let (fl, fr) = frag sproj s
                          in (fl @ ipl, fr @ ipr)

-- Cloud state : plain or frag
data CState : Type where
  Plain : Loc ip Schema -> CState
  FragV  : Loc ipl Schema -> Loc ipr Schema -> CState

data CEnv : CState -> Type where
  MkPEnv : (s : Schema) -> (ip : String) ->
           CEnv (Plain $ s @ ip)
  MkFEnv : (ipl : String) -> (ipr : String) ->
           (sproj : Schema) ->
           CEnv $ (uncurry FragV) (fragWIp sproj s ipl ipr)

data Guard : Effect where
  Encrypt : (k : String) -> (a : Attribute) ->
            Guard ()
                  (CEnv $ Plain $ s@ip)
                  (\_ => CEnv $ Plain $ (encrypt a s)@ip)
  Frag    : (ipl : String) -> (ipr : String) -> (sproj : Schema) ->
            Guard ()
                  (CEnv $ Plain $ s'@ip)
                  (\_ => CEnv $ (uncurry FragV) (fragWIp sproj s ipl ipr))
  Query   : (q : RA (s@ip) -> RA (s'@ip')) ->
            {auto ok : NonEmpty s'} ->
            Guard (Expr ((liftSchU s')@ip'))
                  (CEnv $ Plain $ s@ip)
                  (\_ => CEnv $ Plain $ s@ip)
  QueryL  : (q : RA (sl@ipl) -> RA (sl'@ipl')) ->
            {auto ok : NonEmpty sl'} ->
            Guard (Expr ((liftSchU sl') @ ipl'))
                  (CEnv $ FragV (sl@ipl) (sr@ipr))
                  (\_ => CEnv $ FragV (sl@ipl) (sr@ipr))
  QueryR  : (q : RA (sr@ipr) -> RA (sr'@ipr')) ->
            {auto ok : NonEmpty sr'} ->
            Guard (Expr ((liftSchU sr')@ipr'))
                  (CEnv $ FragV (sl@ipl) (sr@ipr))
                  (\_ => CEnv $ FragV (sl@ipl) (sr@ipr))

GUARD : CState -> EFFECT
GUARD x = MkEff (CEnv x) Guard

encrypt : String -> (a : Attribute) ->
          Eff () [GUARD $ Plain $ s@ip]
                 [GUARD $ Plain $ (encrypt a s)@ip]
encrypt k a = call (Encrypt k a)

frag : (ipl : String) -> (ipr : String) -> (sproj : Schema) ->
       Eff () [GUARD $ Plain (s@ip)]
              [GUARD $ (uncurry FragV) (fragWIp sproj s ipl ipr)]
frag ipl ipr sproj = call (Frag ipl ipr sproj)

query : (RA (s@ip) -> RA (s'@ip')) ->
        {auto ok : NonEmpty s'} ->
        Eff (Expr ((liftSchU s')@ip')) [GUARD $ Plain $ s@ip]
query q = call (Query q)

queryL : (RA (sl@ipl) -> RA (sl'@ipl')) ->
         {auto ok : NonEmpty sl'} ->
          Eff (Expr ((liftSchU sl')@ipl')) [GUARD $ FragV (sl@ipl) (sr@ipr)]
queryL q = call (QueryL q)

queryR : (RA (sr@ipr) -> RA (sr'@ipr')) ->
         {auto ok : NonEmpty sr'} ->
         Eff (Expr ((liftSchU sr')@ipr')) [GUARD $ FragV (sl@ipl) (sr@ipr)]
queryR q = call (QueryR q)

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
