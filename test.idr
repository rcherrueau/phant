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

LeftFragTy : Schema @ "fl"
LeftFragTy = [D,Id] @@ "fl"

RightFragTy : Schema @ "fr"
RightFragTy = [N_c, A, Id] @@ "fr"

-- protectAg : Eff () [GUARD $ Plain $ [D,N,A]@@"cloud"]
--                    [GUARD $ FragV LeftFragTy RightFragTy]
-- protectAg = do encrypt "mykey" N
--                frag "fl" "fr" [D] {inc=includeSingleton Here}

queryOnD : Eff (RA [D,Id]@"fl") [GUARD $ FragV LeftFragTy (sr @@ ipr)]
queryOnD = queryL (Select (\(d :: _) => True) {inc=includeSelf [D,Id]})

queryOnNA : Eff (RA [Id]@"fr") [GUARD $ FragV (sl @@ ipl) RightFragTy]
queryOnNA = queryR ((Project [Id] {inc=includeSingleton (There (There Here))}) .
                    (Select (\(n :: _) => n == encrypt "mykey" "Bob")
                            {inc=includeSelf [N_c,A,Id]}))

-- lFirstStrat : Eff (LocTy $ RA [D,Id]@"local") [GUARD $ Plain $ [D,N,A]@"cloud"]
--                                               [GUARD $ FragV LeftFragTy RightFragTy]
-- lFirstStrat = do encrypt "mykey" N                               --
--                  frag "fl" "fr" [D] {inc=includeSingleton Here}  -- protectAg
--                  ql <- queryOnD
--                  qr <- queryOnNA
--                  pure $ ?njoin ql qr
lFirstStrat : Eff (RA [D,Id]@"fl") [GUARD $ Plain $ [D,N,A]@@"cloud"]
                                   [GUARD $ FragV LeftFragTy RightFragTy]
lFirstStrat = do encrypt "mykey" N                               --
                 frag "fl" "fr" [D] {inc=includeSingleton Here}  -- protectAg
                 ql <- queryOnD
                 qr <- queryOnNA
                 pure ql

-- Can I get the list of attribute, the state of the cloud and the
-- list of pc, from a Guard effect ? Yes for the list of attribute and
-- the cloud state :
--
-- > testPV : Eff r [GUARD $ Plain $ s@@ip] [GUARD $ FragV (sl@@ipl) (sr@@ipr)] -> (Schema, CState, List Schema)
-- > testPV x {s} {sl} {ipl} {sr} {ipr} = (s, FragV (sl @@ ipl) (sr @@ ipr), [])
--
-- If I take the list of attribute in arguments, then I can generate
-- all the first part of the file. Let's do this, but first define
-- what is a list of pc:
--
PC : Type
PC = List Attribute

-- The prelude of a pv file should look like something like this
-- genConfSch : Schema -> List Schema
-- genConfSch []        = [[]]
-- genConfSch (x :: xs) = ?genConfSch_rhs_2

-- hasPC : Schema -> PC -> Bool
-- hasPC []        pc = True
-- hasPC (x :: xs) pc = (elem x pc) && (hasPC xs pc)

-- hasPCs : Schema -> PCs -> PCs
-- hasPCs s []          = []
-- hasPCs s (pc :: pcs) with (hasPC s pc)
--   hasPCs s (pc :: pcs) | False = hasPCs s pcs
--   hasPCs s (pc :: pcs) | True = pc :: (hasPCs s pcs)

prelude : Schema -> List PC -> IO ()
prelude s pcs = do putStrLn "(* Database attributes *)"
                   dbAttributes (names s)
                   putStrLn "(* Privacy constraints *)"
                   pConstraints (map names pcs)
                   putStrLn "(* Instruction for an attacker: what is a PC *)"
                   -- genConfidentials s pcs
  where
  dbAttributes : List String -> IO ()
  dbAttributes []        = putStrLn ""
  dbAttributes (a :: as) =
                  do putStrLn ("const " ++ a ++ ": bistring [private].")
                     dbAttributes as

  pConstraints : List (List String) -> IO ()
  pConstraints []        = putStrLn ""
  pConstraints (x :: xs) =
                  do let pcId = "pc_" ++ (concat x)
                     putStrLn ("const " ++ pcId ++ ": bitstring [private].")
                     putStrLn ("query attacker(" ++ pcId ++ ").")
                     pConstraints xs

  -- printRed : Schema -> List PC -> IO ()
  -- printRed s pcs with (hasAnyBy (\x,y:))
  --   printRed s pcs | with_pat = ?mlkj_rhs

  -- genConfidentials : Schema -> PCs -> IO ()
  -- genConfidentials s pcs = case genConfSch s of
  --                               []          => putStrLn ""
  --                               (s' :: ss') => case hasPCs s' pcs of
  --                                                 [] => putStrLn ""
  --                                                 pcs' => printRed s pcs'




-- Good! Now, let's generate the code from this information
genPV : List PC -> Eff main [GUARD $ Plain (s @@ ip)] [GUARD cstate] -> IO ()
genPV pcs eff {s} {cstate = (Plain (s' @@ ip))} = prelude s pcs
genPV pcs eff {s} {cstate = (FragV (sl @@ ipl) (sr @@ ipr))} = prelude s pcs


test1 : Eff () [GUARD $ Plain $ [D,N,A]@@"cloud"]
               [GUARD $ Plain $ [D,N_c,A]@@"cloud"]
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

-- instance Handler Guard IO where
--     handle (MkPEnv s ip) (Encrypt x a) k =
--            do putStrLn "Encrypt"
--               k () (MkPEnv (encrypt a s) ip)
--     handle (MkPEnv s' ip) (Frag ipl ipr s inc) k =
--            do putStrLn "Frag"
--               k () (MkFEnv ipl ipr s inc)
--     handle (MkPEnv s ip) (Query q) k =
--            do putStrLn "Query"
--               let q' = q (Unit s)
--               k (q' @@ ip) (MkPEnv s ip)
--     handle (MkFEnv ipl ipr s inc) (QueryL q) k =
--            do putStrLn "QueryL"
--               let q' = q (Unit (indexing s))
--               k (q' @@ ipl) (MkFEnv ipl ipr s inc)
--     handle (MkFEnv ipl ipr s inc {s'}) (QueryR q) k =
--            do putStrLn "QueryR"
--               let q' = q (Unit (indexing (s' \\ s)))
--               k (q' @@ ipr) (MkFEnv ipl ipr s inc)

-- instance Handler Guard List where
--   handle r (Encrypt x y) k = [] -- ?Handler_rhs_2
--   handle r (Frag ipl ipr s inc) k = [] --?Handler_rhs_3
--   handle r (Query q) k = [] --?Handler_rhs_4
--   handle r (QueryL q) k = [] --?Handler_rhs_5
--   handle r (QueryR q) k = [] --?Handler_rhs_6

-- runTest1 : IO ()
-- runTest1 = runInit [ (MkPEnv [D,N,A] "cloud") ] test1

-- runTest2 : (bd : CEnv $ Plain $ s@@ip) -> Eff (RA s'@ip') [GUARD $ Plain $ s@@ip ] [GUARD r] -> IO ()
-- runTest2 bd x {s'} {ip'} = do av <- the (IO (RA s'@ip')) $ runInit [bd] x
--                               let v = getVal av
--                               eval v

main : IO ()
-- main = runTest2 (MkPEnv [D,N,A] "cloud") lFirstStrat
main = do let PCs =  [[N],[D,A]]
          genPV PCs lFirstStrat
          putStrLn "-----------------------"
          genPV PCs test1
-- main = putStrLn "test"


-- λΠ> the (IO (LocTy $ RA [D,Id] @ "fl")) $ runInit [MkPEnv [D,N,A] "cloud" ] lFirstStrat

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
