module Main

import crypt
import pv
import guard
import Effects

D : Attribute
D = ("Date", NAT)

N : Attribute
N = ("Name", TEXT 255)

Nc : Attribute
Nc = ("Name", CRYPT (TEXT 255))

A : Attribute
A = ("Addr", TEXT 255)

-- LeftFragTy : Schema @ "fl"
-- LeftFragTy = [D,Id] @@ "fl"

-- RightFragTy : Schema @ "fr"
-- RightFragTy = [Nc, A, Id] @@ "fr"

-- protectAg : Eff () [GUARD $ Plain $ [D,N,A]@@"cloud"]
--                    [GUARD $ FragV LeftFragTy RightFragTy]
-- protectAg = do encrypt "mykey" N
--                frag "fl" "fr" [D] {inc=includeSingleton Here}

places : Eff (RA [A] @ "cloud") [GUARD $ Plain $ [D, Nc, A] @@ "cloud"]
places = do
  encrypt "mykey" N
  query ((Project [A]
                  {inc=includeSingleton (There (There Here))}) .
         (Select (\(_ :: _ :: a :: _) => True)
                 {inc=includeSelf [D,Nc,A]}))

meetings : Eff (RA [Nc] @ "cloud") [GUARD $ Plain $ [D, Nc, A] @@ "cloud"]
meetings = do
  let contact = the (AES String) $ encrypt "mykey" "Bob"
  encrypt "mykey" N
  query ((Project [Nc] {inc=includeSingleton (There Here)}).
         (Select (\(_ :: nc :: _) => nc == contact)
                 {inc=includeSelf [D,Nc,A]}))


-- queryOnD : Eff (RA [D,Id]@"fl") [GUARD $ FragV LeftFragTy (sr @@ ipr)]
-- queryOnD = queryL (Select (\(d :: _) => True) {inc=includeSelf [D,Id]})

-- queryOnNA : Eff (RA [Id]@"fr") [GUARD $ FragV (sl @@ ipl) RightFragTy]
-- queryOnNA = queryR ((Project [Id] {inc=includeSingleton (There (There Here))}) .
--                     (Select (\(n :: _) => n == encrypt "mykey" "Bob")
--                             {inc=includeSelf [Nc,A,Id]}))

-- lFirstStrat : Eff (RA [D,Id]@"fl") [GUARD $ Plain $ [D,N,A]@@"cloud"]
--                                    [GUARD $ FragV LeftFragTy RightFragTy]
-- lFirstStrat = do encrypt "mykey" N                               --
--                  frag "fl" "fr" [D] {inc=includeSingleton Here}  -- protectAg
--                  ql <- queryOnD
--                  qr <- queryOnNA
--                  pure ql



-- runTest1 : IO ()
-- runTest1 = runInit [ (MkPEnv [D,N,A] "cloud") ] test1

-- runTest2 : (bd : CEnv $ Plain $ s@@ip) -> Eff (RA s'@ip') [GUARD $ Plain $ s@@ip ] [GUARD r] -> IO ()
-- runTest2 bd x {s'} {ip'} = do av <- the (IO (RA s'@ip')) $ runInit [bd] x
--                               let v = getVal av
--                               eval v

main : IO ()
-- main = runTest2 (MkPEnv [D,N,A] "cloud") lFirstStrat
main = do let PCs =  [[N],[D,A]]
          genPV PCs places
          -- genPV PCs lFirstStrat
--           putStrLn "-----------------------"
--           genPV PCs test1
-- main = putStrLn "lala"


-- λΠ> the (IO (LocTy $ RA [D,Id] @ "fl")) $ runInit [MkPEnv [D,N,A] "cloud" ] lFirstStrat

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
