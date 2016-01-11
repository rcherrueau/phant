module phant.guard

import public utils
import public schema
import public ra

import public crypt

import public Effects
import Data.List

%default total
%access public

fragWTag : (sproj : Schema) -> (s : Schema) -> (ipl,ipr : Tag) -> (Tagged ipl Schema, Tagged ipr Schema)
fragWTag sproj s ipl ipr = let (fl, fr) = frag sproj s
                           in (fl @@ ipl, fr @@ ipr)

-- Cloud state : plain or frag
data CState : Type where
  Plain  : Tagged ip Schema -> CState
  FragV  : Tagged ipl Schema -> Tagged ipr Schema -> CState

data CEnv : CState -> Type where
  MkPEnv : (s : Schema) -> (ip : Tag) -> CEnv (Plain (s @@ ip))
  MkFEnv : (sproj : Schema) -> (ipl,ipr : Tag) -> CEnv $ (uncurry FragV) (fragWTag sproj s ipl ipr )


data Guard : Effect where
  -- Protect : (s : Schema) -> (pcs : List PC) ->
  -- Protect : (pcs : List PC) ->
  --           Guard ()
  --                 (r)
  --                 (\_ => r)
  Encrypt : (k : String) -> (a : Attribute) ->
            Guard ()
                  (CEnv $ Plain (s @@ ip))
                  (\_ => CEnv $ Plain ((encrypt a s) @@ ip))
  Frag    : (sproj : Schema) ->
            (ipl : Tag) -> (ipr : Tag) ->
            Guard ()
                  (CEnv $ Plain (s @@ ip))
                  (\_ => CEnv $ (uncurry FragV) (fragWTag sproj s ipl ipr))
  Query   : (q : RA (s @@ ip) -> RA (s' @@ ipRes)) ->
            Guard (Expr $ SCH s' @@ ipRes)
                  (CEnv $ Plain (s @@ ip))
                  (\_ => CEnv $ Plain (s @@ ip))
  QueryL  : (q : RA $ sl @@ ipl -> RA $ sl' @@ iplRes) ->
            Guard (Expr $ SCH sl' @@ iplRes)
                  (CEnv $ FragV (sl @@ ipl) (sr @@ ipr))
                  (\_ => CEnv $ FragV (sl @@ ipl) (sr @@ ipr))
  QueryR  : (q : RA $ sr @@ ipr -> RA $ sr' @@ iprRes) ->
            Guard (Expr $ SCH sr' @@ iprRes)
                  (CEnv $ FragV (sl @@ ipl) (sr @@ ipr))
                  (\_ => CEnv $ FragV (sl @@ ipl)  (sr @@ ipr))

GUARD : CState -> EFFECT
GUARD x = MkEff (CEnv x) Guard

-- -- protect : (s : Schema) -> (pcs : List PC) -> Eff () [GUARD $ PCs pcs] [GUARD $ Plain s]
-- -- protect s pcs = call (Protect s pcs)
-- -- protect : (pcs : List PC) -> Eff () [GUARD $ Plain s]
-- -- protect pcs = call (Protect pcs)

encrypt : String -> (a : Attribute) -> Eff () [GUARD $ Plain (s @@ ip)]
                                              [GUARD $ Plain ((encrypt a s) @@ ip)]
encrypt k a = call (Encrypt k a)

frag : (sproj : Schema) -> (ipl,ipr: Tag) ->
       Eff () [GUARD $ Plain (s @@ ip)]
              [GUARD $ (uncurry FragV) (fragWTag sproj s ipl ipr)]
frag sproj ipl ipr = call (Frag sproj ipl ipr)

query : (RA (s @@ ip) -> RA (s' @@ ipRes)) ->
        Eff (Expr $ SCH s' @@ ipRes) [GUARD $ Plain (s @@ ip)]
query q = call (Query q)

queryL : (RA (sl @@ ipl) -> RA (sl' @@ iplRes)) ->
         Eff (Expr $ SCH sl' @@ iplRes) [GUARD $ FragV (sl @@ ipl) (sr @@ ipr)]
queryL q = call (QueryL q)

queryR : (RA (sr @@ ipr) -> RA (sr' @@ iprRes)) ->
         Eff (Expr $ SCH sr' @@ iprRes) [GUARD $ FragV (sl @@ ipl) (sr @@ ipr)]
queryR q = call (QueryR q)

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
