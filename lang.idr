import Effects
import psql

%default total

Id : Attribute
Id = ("Id", NAT)

infix 5 @
data Loc : (a : Type) -> Type where
     (@) :  a -> (ip : String) -> Loc a

getIp : Loc a -> String
getIp ((@) x ip) = ip

data LocIp : (a : Type) -> String -> Type  where
     MkLocIp : (l : Loc a) -> LocIp a (getIp l)

map : (a -> a) -> Loc a -> Loc a
map f ((@) x ip) = f x @ ip

-- Cloud state : plain or frag
data CState : Type where
     Plain : Loc Schema -> CState
     Frag  : Loc Schema -> Loc Schema -> CState

-- data LocTy : Loc a -> Type where
--      MkLocTy : (l : Loc a) -> LocTy l

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
                     (\x => CEnv $ Frag (Id :: (intersect s s')@ipFL)
                                        (Id :: (s' \\ s)@ipFR))
     Encrypt : (a : String) ->
               Guard ()
                     (CEnv $ Plain (s@ip))
                     (\x => CEnv $ Plain ((encryptSc a s)@ip))
     Query   : (q: RA s -> RA s') ->
               Guard (LocIp (RA s') ip)
                     (CEnv $ Plain (s@ip))
                     (\x => CEnv $ Plain (s@ip))
     QueryL  : (q: RA sL -> RA sL') ->
               Guard (LocIp (RA sL') ip)
                     (CEnv $ Frag (sL@ip) fR)
                     (\x => CEnv $ Frag (sL@ip) fR)
     QueryR  : (q: RA sR -> RA sR') ->
               Guard (LocIp (RA sR') ip)
                     (CEnv $ Frag fL (sR@ip))
                     (\x => CEnv $ Frag fL (sR@ip))

GUARD : CState -> EFFECT
GUARD x = MkEff (CEnv x) Guard

frag : (s : Schema) -> (ipL : String) -> (ipR : String) ->
       Eff () [GUARD $ Plain (s'@ip)]
              [GUARD $ Frag (Id :: (intersect s s')@ipL)
                            (Id :: (s' \\ s)@ipR)]
frag s ipL ipR = call (FragV s ipL ipR)

encrypt : (a : String) -> Eff () [GUARD $ Plain (s@ip)]
                                 [GUARD $ Plain ((encryptSc a s)@ip)]
encrypt a = call (Encrypt a)

query : (RA s -> RA s') -> Eff (LocIp (RA s') ip) [GUARD $ Plain (s@ip)]
query q = call (Query q)

queryL : (RA sL -> RA sL') -> Eff (LocIp (RA sL') ip) [GUARD $ Frag (sL@ip) sR]
queryL q = call (QueryL q)

queryR : (RA sR -> RA sR') -> Eff (LocIp (RA sR') ip) [GUARD $ Frag sL (sR@ip)]
queryR q = call (QueryR q)

test1 : Eff (LocIp (RA s) ip) [GUARD (Plain (s@ip))]
test1 = query (id)

D : Attribute
D = ("Date", TEXT 10)

N : Attribute
N = ("Name", TEXT 255)

NC : Attribute
NC = ("Name", CRYPT)

A : Attribute
A = ("Addr", NAT)

ScAg : Schema
ScAg = [D,N,A]

protectAg : Eff () [GUARD $ Plain (ScAg@"1.1.1.1")]
                   [GUARD $ Frag  ?FragLeftTy ?FragRightTy]
protectAg = do encrypt "Name"
               frag [D] "1.1.1.2" "1.1.1.3"

-- :printdef FRType
-- FragLeftTy  = %runElab search
-- FragRightTy = %runElab search
FragLeftTy  = [Id,D]@"1.1.1.2"
FragRightTy = [Id,NC,A]@"1.1.1.3"

-- queryOnFL : Eff (LocTy $ RA [Id,D]@"1.1.1.2") [GUARD $ Frag ([Id,D]@"1.1.1.2") fragR]
queryOnFL : Eff (LocIp (RA [Id,D]) "1.1.1.2") [GUARD $ Frag Main.FragLeftTy fragR]
queryOnFL = queryL (Select (\(_ |: d |: _) => True))

-- queryOnFR : Eff (LocTy $ RA [Id]@"1.1.1.3") [GUARD $ Frag fragL ([NC,A,Id]@"1.1.1.3")]
queryOnFR : Eff (LocIp (RA [Id]) "1.1.1.3") [GUARD $ Frag fragL Main.FragRightTy]
queryOnFR = queryR (Project [Id] .
                    Select (\(_ |: n |: _) =>
                    -- > Type mismatche between String and AES
                    -- n == "Alice"))
                    -- > Can't resolve type class Ord (AES)
                    -- n >= (encrypt "mickey" "Alice")))
                    -- > OK
                    n == (encrypt "mickey" "Alice")))

lFirstStrat : Eff (LocIp (RA [Id,D]) "local") [GUARD $ Plain (ScAg@"1.1.1.1")]
                                              [GUARD $ Frag  Main.FragLeftTy Main.FragRightTy]
lFirstStrat = do protectAg
                 qL <- queryOnFL
                 qR <- queryOnFR
                 pure $ njoin qL qR
  where
  -- better: defrag↓
  njoin : LocIp (RA s) ipL -> LocIp (RA s') ipR ->
          LocIp (RA (nubBy (\a1,a2 => (fst a1) == (fst a2)) (s ++ s'))) "local"
  njoin (MkLocIp ((@) qL ipL)) (MkLocIp ((@) qR ipR)) = MkLocIp $ (Join qL qR)@"local"

  -- ⵑ : 0x2D51
  defragⵑ :
    LocIp (RA s) ipL -> LocIp (RA s') ipR ->
    LocIp (RA (nubBy (\a1,a2 => (fst a1) == (fst a2)) (s ++ s'))) "local"
  defragⵑ (MkLocIp ((@) qL ipL)) (MkLocIp ((@) qR ipR)) = MkLocIp $ (Join qL qR)@"local"


-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
