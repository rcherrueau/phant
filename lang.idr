import Effects

import psql

-- Cloud state : plain or frag
data CState : Type where
     Plain : Schema -> CState
     Frag  : Schema -> Schema -> CState

-- Cloud Environement
data CEnv : CState -> Type

encryptSc : String -> Schema -> Schema
encryptSc n []              = []
encryptSc n ((n',t) :: xs) with (n == n')
  encryptSc n ((n',t) :: xs) | False = (n',t) :: (encryptSc n xs)
  encryptSc n ((n',t) :: xs) | True  = (n', CRYPT) :: xs

data Guard : Effect where
     FragV   : (s : Schema) ->
               Guard ()       (CEnv $ Plain s')
                              (\x => CEnv $ Frag (intersect s s') (s' \\ s))
     Encrypt : (a : String) ->
               Guard ()       (CEnv $ Plain s)
                              (\x => CEnv $ Plain (encryptSc a s))
     Query   : (q: RA s -> RA s') ->
               Guard (RA s')  (CEnv $ Plain s)
                              (\x => CEnv $ Plain s)
     QueryL  : (q: RA sL -> RA sL') ->
               Guard (RA sL') (CEnv $ Frag sL sR)
                              (\x => CEnv $ Frag sL sR)
     QueryR  : (q: RA sR -> RA sR') ->
               Guard (RA sR') (CEnv $ Frag sL sR)
                              (\x => CEnv $ Frag sL sR)

GUARD : CState -> EFFECT
GUARD x = MkEff (CEnv x) Guard

frag : (s : Schema) -> Eff () [GUARD $ Plain s'] [GUARD $ Frag (intersect s s')(s' \\ s)]
frag s = call (FragV s)

encrypt : (a : String) -> Eff () [GUARD $ Plain s] [GUARD $ Plain (encryptSc a s)]
encrypt a = call (Encrypt a)

query : (RA s -> RA s') -> Eff (RA s') [GUARD $ Plain s]
query q = call (Query q)

queryL : (RA sL -> RA sL') -> Eff (RA sL') [GUARD $ Frag sL sR]
queryL q = call (QueryL q)

queryR : (RA sR -> RA sR') -> Eff (RA sR') [GUARD $ Frag sL sR]
queryR q = call (QueryR q)

test1 : Eff (RA s) [GUARD (Plain s)]
test1 = query (id)

test2 : Eff (RA [("date", TEXT 10)]) [GUARD $ Plain [("date", TEXT 10),
                                                     ("name", TEXT 255),
                                                     ("addr", NAT),
                                                     ("id", NAT)]]
                                     [GUARD $ Frag  [("date", TEXT 10)]
                                                    [("name", CRYPT),
                                                     ("addr", NAT),
                                                     ("id", NAT)]]
test2 = do encrypt "name"
           frag [("date", TEXT 10)]
           queryL (Select (\(d |: RNil) => True))

test3 : Eff (RA [("id", NAT)]) [GUARD $ Frag  [("date", TEXT 10)]
                                              [("name", CRYPT),
                                               ("addr", NAT),
                                               ("id", NAT)]]
test3 = queryR (Project [("id", NAT)] .
                Select (\(n |: a |: id |: RNil) => True))



-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
