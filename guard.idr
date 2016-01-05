module phant.guard

import public utils
import public schema
import public table
import public ra

import Effects
import Data.List

%default total
%access public

infix 5 @
infix 5 @@

-- abstract -- to keep constructor private
data (@) : (a : Type) -> (ip : String) -> Type where
  (@@) : (v : a) -> (ip : String) -> a @ ip

getVal : a @ ip -> a
getVal (v @@ ip) = v

getIp : a @ ip -> String
getIp _ {ip} = ip

map : (a -> b) -> a @ ip -> b @ ip
map f (v @@ ip) = f v @@ ip

local : a -> a @ "local"
local x = x @@ "local"

-- Cloud state : plain or frag
data CState : Type where
  Plain : Schema @ ip -> CState
  FragV  : Schema @ ipl -> Schema @ ipr -> CState

data CEnv : CState -> Type where
  MkPEnv : (s : Schema) -> (ip : String) ->
           CEnv (Plain $ s @@ ip)
  MkFEnv : (ipl : String) -> (ipr : String) ->
           (s : Schema) -> (inc : Include s s') ->
           CEnv (FragV ((indexing s)@@ipl) ((indexing (s' \\ s))@@ipr))

data Guard : Effect where
  Encrypt : (k : String) -> (a : Attribute) ->
            Guard ()
                  (CEnv $ Plain $ s@@ip)
                  (\_ => CEnv $ Plain $ (encrypt a s)@@ip)
  Frag    : (ipl : String) -> (ipr : String) -> (s : Schema) ->
            (inc : Include s s') ->
            Guard ()
                  (CEnv $ Plain $ s'@@ip)
                  -- (\_ => CEnv $ (uncurry FragV) $ map2 (flip (@@) ipl)
                  --                                      (flip (@@) ipr)
                  --                                      (frag s s' {inc}))
                  (\_ => CEnv $ FragV ((indexing s)@@ipl) ((indexing (s' \\ s))@@ipr))
  Query   : (q : RA s -> RA s') ->
            Guard (RA s' @ ip)
                  (CEnv $ Plain $ s@@ip)
                  (\_ => CEnv $ Plain $ s@@ip)
  QueryL  : (q : RA sl -> RA sl') ->
            Guard (RA sl' @ ipl)
                  (CEnv $ FragV (sl@@ipl) (sr@@ipr))
                  (\_ => CEnv $ FragV (sl@@ipl) (sr@@ipr))
  QueryR  : (q : RA sr -> RA sr') ->
            Guard (RA sr'@ipr)
                  (CEnv $ FragV (sl@@ipl) (sr@@ipr))
                  (\_ => CEnv $ FragV (sl@@ipl) (sr@@ipr))

GUARD : CState -> EFFECT
GUARD x = MkEff (CEnv x) Guard

encrypt : String -> (a : Attribute) ->
          Eff () [GUARD $ Plain $ s@@ip]
                 [GUARD $ Plain $ (encrypt a s)@@ip]
encrypt k a = call (Encrypt k a)

frag : (ipl : String) -> (ipr : String) -> (s : Schema) ->
       {auto inc : Include s s'} ->
       Eff () [GUARD $ Plain (s'@@ip)]
              -- [GUARD $ (uncurry FragV) $ map2 (flip (@) ipl)
              --                                 (flip (@) ipr)
              --                                 (frag s s' {inc})]
              [GUARD $ FragV ((indexing s)@@ipl) ((indexing (s' \\ s))@@ipr)]
frag ipl ipr s {inc} = call (Frag ipl ipr s inc)

query : (RA s -> RA s') -> Eff (RA s'@ip) [GUARD $ Plain $ s@@ip]
query q = call (Query q)

queryL : (RA sl -> RA sl') -> Eff (RA sl'@ipl) [GUARD $ FragV (sl@@ipl) (sr@@ipr)]
queryL q = call (QueryL q)

queryR : (RA sr -> RA sr') -> Eff (RA sr'@ipr) [GUARD $ FragV (sl@@ipl) (sr@@ipr)]
queryR q = call (QueryR q)


-- -- runEval : Eff s [GUARD g] -> List ?find_me
-- -- runEval x = ?runEval_rhs

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
