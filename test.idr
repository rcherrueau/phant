module Main

import guard
import Effects

D : Attribute
D = ("Date", NAT)

N : Attribute
N = ("Name", TEXT 255)

N_c : Attribute
N_c = ("Name", CRYPT (TEXT 255))

A : Attribute
A = ("Addr", TEXT 255)

LeftFragTy : Loc Schema
LeftFragTy = [D,Id] @ "fl"

RightFragTy : Loc Schema
RightFragTy = [N_c, A, Id] @ "fr"

-- protectAg : Eff () [GUARD $ Plain $ [D,N,A]@"cloud"]
--                    [GUARD $ FragV LeftFragTy RightFragTy]
-- protectAg = do encrypt "mykey" N
--                frag "fl" "fr" [D] {inc=includeSingleton Here}

-- queryOnD : Eff (LocTy $ RA [D,Id]@"fl") [GUARD $ FragV LeftFragTy _]
-- queryOnD = queryL (Select (\(d :: _) => True) {inc=includeSelf [D,Id]})

-- queryOnNA : Eff (LocTy $ RA [Id]@"fr") [GUARD $ FragV _ RightFragTy]
-- queryOnNA = queryR ((Project [Id] {inc=includeSingleton (There (There Here))}) .
--                     (Select (\(n :: _) => n == encrypt "mykey" "Bob")
--                             {inc=includeSelf [N_c,A,Id]}))

-- -- lFirstStrat : Eff (LocTy $ RA [D,Id]@"local") [GUARD $ Plain $ [D,N,A]@"cloud"]
-- --                                               [GUARD $ FragV LeftFragTy RightFragTy]
-- -- lFirstStrat = do encrypt "mykey" N                               --
-- --                  frag "fl" "fr" [D] {inc=includeSingleton Here}  -- protectAg
-- --                  ql <- queryOnD
-- --                  qr <- queryOnNA
-- --                  pure $ ?njoin ql qr
-- lFirstStrat : Eff (LocTy $ RA [D,Id]@"fl") [GUARD $ Plain $ [D,N,A]@"cloud"]
--                                               [GUARD $ FragV LeftFragTy RightFragTy]
-- lFirstStrat = do encrypt "mykey" N                               --
--                  frag "fl" "fr" [D] {inc=includeSingleton Here}  -- protectAg
--                  ql <- queryOnD
--                  qr <- queryOnNA
--                  pure ql

test1 : Eff () [GUARD $ Plain $ [D,N,A]@"cloud"]
               [GUARD $ Plain $ [D,N_c,A]@"cloud"]
test1 = encrypt "toto" N

-- instance Handler Guard m where
--     handle (MkPEnv s ip) (Encrypt x a) k = k () (MkPEnv (encrypt a s) ip)
--     handle (MkPEnv s' ip) (Frag ipl ipr s inc) k = k () (MkFEnv ipl ipr s inc)
--     handle (MkPEnv s ip) (Query q) k =
--            let qRes = q (Unit s)
--                qLTy = MkLocTy (qRes @ ip)
--            in k qLTy (MkPEnv s ip)
--     handle (MkFEnv ipl ipr s inc) (QueryL q) k =
--            let qRes = q (Unit (indexing s))
--                qLTy = MkLocTy (qRes @ ipl)
--            in k qLTy (MkFEnv ipl ipr s inc)
--     handle (MkFEnv ipl ipr s inc {s'}) (QueryR q) k =
--            let qRes = q (Unit (indexing (s' \\ s)))
--                qLTy = MkLocTy (qRes @ ipr)
--            in k qLTy (MkFEnv ipl ipr s inc)


instance Handler Guard IO where
    handle (MkPEnv s ip) (Encrypt x a) k =
           do putStrLn "Encrypt"
              k () (MkPEnv (encrypt a s) ip)
    handle (MkPEnv s' ip) (Frag ipl ipr s inc) k =
           do putStrLn "Frag"
              k () (MkFEnv ipl ipr s inc)
    handle (MkPEnv s ip) (Query q) k =
           do putStrLn "Query"
              let qRes = q (Unit s)
              let qLTy = MkLocTy (qRes @ ip)
              k qLTy (MkPEnv s ip)
    handle (MkFEnv ipl ipr s inc) (QueryL q) k =
           do putStrLn "QueryL"
              let qRes = q (Unit (indexing s))
              let qLTy = MkLocTy (qRes @ ipl)
              k qLTy (MkFEnv ipl ipr s inc)
    handle (MkFEnv ipl ipr s inc {s'}) (QueryR q) k =
           do putStrLn "QueryR"
              let qRes = q (Unit (indexing (s' \\ s)))
              let qLTy = MkLocTy (qRes @ ipr)
              k qLTy (MkFEnv ipl ipr s inc)

-- instance Handler Guard List where
--   handle r (Encrypt x y) k = [] -- ?Handler_rhs_2
--   handle r (Frag ipl ipr s inc) k = [] --?Handler_rhs_3
--   handle r (Query q) k = [] --?Handler_rhs_4
--   handle r (QueryL q) k = [] --?Handler_rhs_5
--   handle r (QueryR q) k = [] --?Handler_rhs_6

runTest1 : IO ()
runTest1 = runInit [ (MkPEnv [D,N,A] "cloud") ] test1

runTest2 : (bd : CEnv $ Plain $ s@ip) -> Eff (LocTy $ RA s'@ip') [GUARD $ Plain $ s@ip ] -> IO ()
runTest2 bd x {s'} {ip'} = let a  = the (IO (LocTy $ RA s'@ip')) $ runInit [bd] x
                           in case (unsafePerformIO a) of
                                   (MkLocTy (ra @ ip)) => eval ra
  where
  eval : RA s' -> IO ()



-- λΠ> the (IO (LocTy $ RA [D,Id] @ "fl")) $ runInit [MkPEnv [D,N,A] "cloud" ] lFirstStrat

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
