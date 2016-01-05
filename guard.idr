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
infix 5 :@:

data Loc : (a : Type) -> Type where
  (@) :  a -> (ip : String) -> Loc a

getIp : Loc a -> String
getIp ((@) x ip) = ip

getA : {a : Type} -> Loc a -> a
getA ((@) x ip) = x

-- `abstract` to keep constroctor inside this file
abstract data LocIp : (a : Type) -> String -> Type  where
  MkLocIp : (l : Loc a) -> LocIp a (getIp l)

data LocTy : Loc a -> Type where
  MkLocTy : (l : Loc a) -> LocTy (a @ (getIp l))

getLocA : {l : Loc a} -> LocTy l -> a
getLocA _ {l} = getA l

map : (a -> b) -> Loc a -> Loc b
map f ((@) x ip) = f x @ ip

-- Cloud state : plain or frag
data CState : Type where
  Plain : Loc Schema -> CState
  FragV  : Loc Schema -> Loc Schema -> CState

data CEnv : CState -> Type where
  MkPEnv : (s : Schema) -> (ip : String) ->
           CEnv (Plain $ s @ ip)
  MkFEnv : (ipl : String) -> (ipr : String) ->
           (s : Schema) -> (inc : Include s s') ->
           CEnv (FragV ((indexing s)@ipl) ((indexing (s' \\ s))@ipr))

data Guard : Effect where
  Encrypt : (k : String) -> (a : Attribute) ->
            Guard ()
                  (CEnv $ Plain $ s@ip)
                  (\_ => CEnv $ Plain $ (encrypt a s)@ip)
  Frag    : (ipl : String) -> (ipr : String) -> (s : Schema) ->
            (inc : Include s s') ->
            Guard ()
                  (CEnv $ Plain $ s'@ip)
                  -- (\_ => CEnv $ (uncurry FragV) $ map2 (flip (@) ipl)
                  --                                      (flip (@) ipr)
                  --                                      (frag s s' {inc}))
                  (\_ => CEnv $ FragV ((indexing s)@ipl) ((indexing (s' \\ s))@ipr))
  Query   : (q : RA s -> RA s') ->
            Guard (LocTy $ RA s'@ip)
                  (CEnv $ Plain $ s@ip)
                  (\_ => CEnv $ Plain $ s@ip)
  QueryL  : (q : RA sl -> RA sl') ->
            Guard (LocTy $ RA sl'@ip)
                  (CEnv $ FragV (sl@ip) r)
                  (\_ => CEnv $ FragV (sl@ip) r)
  QueryR  : (q : RA sr -> RA sr') ->
            Guard (LocTy $ RA sr'@ip)
                  (CEnv $ FragV l (sr@ip))
                  (\_ => CEnv $ FragV l (sr@ip))

GUARD : CState -> EFFECT
GUARD x = MkEff (CEnv x) Guard

encrypt : String -> (a : Attribute) ->
          Eff () [GUARD $ Plain $ s@ip]
                 [GUARD $ Plain $ (encrypt a s)@ip]
encrypt k a = call (Encrypt k a)

frag : (ipl : String) -> (ipr : String) -> (s : Schema) ->
       {auto inc : Include s s'} ->
       Eff () [GUARD $ Plain (s'@ip)]
              -- [GUARD $ (uncurry FragV) $ map2 (flip (@) ipl)
              --                                 (flip (@) ipr)
              --                                 (frag s s' {inc})]
              [GUARD $ FragV ((indexing s)@ipl) ((indexing (s' \\ s))@ipr)]
frag ipl ipr s {inc} = call (Frag ipl ipr s inc)

query : (RA s -> RA s') -> Eff (LocTy $ RA s'@ip) [GUARD $ Plain $ s@ip]
query q = call (Query q)

queryL : (RA sl -> RA sl') -> Eff (LocTy $ RA sl'@ip) [GUARD $ FragV (sl@ip) r]
queryL q = call (QueryL q)

queryR : (RA sr -> RA sr') -> Eff (LocTy $ RA sr'@ip) [GUARD $ FragV l (sr@ip)]
queryR q = call (QueryR q)


-- runEval : Eff s [GUARD g] -> List ?find_me
-- runEval x = ?runEval_rhs

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
