import Effects
import psql

%default total

infix 5 @
data Loc : (a : Type) -> Type where
     (@) :  a -> (ip : String) -> Loc a


-- Cloud state : plain or frag
data CState : Type where
     Plain : Loc Schema -> CState
     Frag  : Loc Schema -> Loc Schema -> CState

data LocTy : Loc a -> Type

-- Cloud Environement
data CEnv : CState -> Type

encryptSc : String -> Schema -> Schema
encryptSc n []              = []
encryptSc n ((n',t) :: xs) with (n == n')
  encryptSc n ((n',t) :: xs) | False = (n',t) :: (encryptSc n xs)
  encryptSc n ((n',t) :: xs) | True  = (n', CRYPT) :: xs

data Guard : Effect where
     FragV   : (s : Schema) -> (ipFL : String) -> (ipFR : String) ->
               Guard ()
                     (CEnv $ Plain (s'@ip))
                     (\x => CEnv $ Frag ((intersect s s')@ipFL)
                                        ((s' \\ s)@ipFR))
     Encrypt : (a : String) ->
               Guard ()
                     (CEnv $ Plain (s@ip))
                     (\x => CEnv $ Plain ((encryptSc a s)@ip))
     Query   : (q: RA s -> RA s') ->
               Guard (LocTy $ RA s'@ip)
                     (CEnv $ Plain (s@ip))
                     (\x => CEnv $ Plain (s@ip))
     QueryL  : (q: RA sL -> RA sL') ->
               Guard (LocTy $ RA sL'@ip)
                     (CEnv $ Frag (sL@ip) fR)
                     (\x => CEnv $ Frag (sL@ip) fR)
     QueryR  : (q: RA sR -> RA sR') ->
               Guard (LocTy $ RA sR'@ip)
                     (CEnv $ Frag fL (sR@ip))
                     (\x => CEnv $ Frag fL (sR@ip))

GUARD : CState -> EFFECT
GUARD x = MkEff (CEnv x) Guard

frag : (s : Schema) -> (ipFL : String) -> (ipFR : String) ->
       Eff () [GUARD $ Plain (s'@ip)]
              [GUARD $ Frag ((intersect s s')@ipFL)
                            ((s' \\ s)@ipFR)]
frag s ipFL ipFR = call (FragV s ipFL ipFR)

encrypt : (a : String) -> Eff () [GUARD $ Plain (s@ip)]
                                 [GUARD $ Plain ((encryptSc a s)@ip)]
encrypt a = call (Encrypt a)

query : (RA s -> RA s') -> Eff (LocTy $ RA s'@ip) [GUARD $ Plain (s@ip)]
query q = call (Query q)

queryL : (RA sL -> RA sL') -> Eff (LocTy $ RA sL'@ip) [GUARD $ Frag (sL@ip) sR]
queryL q = call (QueryL q)

queryR : (RA sR -> RA sR') -> Eff (LocTy $ RA sR'@ip) [GUARD $ Frag sL (sR@ip)]
queryR q = call (QueryR q)

test1 : Eff (LocTy $ RA s@ip) [GUARD (Plain (s@ip))]
test1 = query (id)

D : Attribute
D = ("Date", TEXT 10)

N : Attribute
N = ("Name", TEXT 255)

NC : Attribute
NC = ("Name", CRYPT)

A : Attribute
A = ("Addr", NAT)

Id : Attribute
Id = ("Id", NAT)

ScAg : Schema
ScAg = [D,N,A,Id]

protectAg : Eff () [GUARD $ Plain (ScAg@"1.1.1.1")]
                   [GUARD $ Frag  ?FragLeftTy ?FragRightTy]
protectAg = do encrypt "Name"
               frag [D] "1.1.1.2" "1.1.1.3"

-- :printdef FRType
-- FragLeftTy  = %runElab search
-- FragRightTy = %runElab search
FragLeftTy  = [D]@"1.1.1.2"
FragRightTy = [NC,A,Id]@"1.1.1.3"

-- queryOnFL : Eff (LocTy $ RA [D]@"1.1.1.2") [GUARD $ Frag ([D]@"1.1.1.2") fragR]
queryOnFL : Eff (LocTy $ RA [D]@"1.1.1.2") [GUARD $ Frag Main.FragLeftTy fragR]
queryOnFL = queryL (Select (\(d |: RNil) => True))

-- queryOnFR : Eff (LocTy $ RA [Id]@"1.1.1.3") [GUARD $ Frag fragL ([NC,A,Id]@"1.1.1.3")]
queryOnFR : Eff (LocTy $ RA [Id]@"1.1.1.3") [GUARD $ Frag fragL Main.FragRightTy]
queryOnFR = queryR (Project [("Id", NAT)] .
                    Select (\(n |: _) =>
                    -- > Type mismatche between String and AES
                    -- n == "Alice"))
                    -- > Can't resolve type class Ord (AES)
                    -- n >= (encrypt "mickey" "Alice")))
                    -- > OK
                    n == (encrypt "mickey" "Alice")))

lFirstStrat : Eff (LocTy $ RA [Id]@"1.1.1.3") [GUARD $ Plain (ScAg@"1.1.1.1")]
                                              [GUARD $ Frag  Main.FragLeftTy Main.FragRightTy]
lFirstStrat = do protectAg
                 qL <- queryOnFL
                 qR <- queryOnFR
                 pure qR


-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
