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

LeftFragTy : Schema @ "fl"
LeftFragTy = [D,Id] @@ "fl"

RightFragTy : Schema @ "fr"
RightFragTy = [Nc, A, Id] @@ "fr"

places : Eff (RA [A] @ "cloud") [GUARD $ Plain $ [D, Nc, A] @@ "cloud"]
places = do
  encrypt "mykey" N
  query (Project [A] .
         Select (\(_ :: _ :: a :: _) => True))

meetings : Eff (RA [Nc] @ "cloud") [GUARD $ Plain $ [D, Nc, A] @@ "cloud"]
meetings = do
  let contact = the (AES String) $ encrypt "mykey" "Bob"
  encrypt "mykey" N
  query (Project [Nc] .
         Select (\(_ :: nc :: _) => nc == contact))

queryOnD : Eff (RA [D,Id]@"fl") [GUARD $ FragV LeftFragTy (sr @@ ipr)]
queryOnD = queryL (Select (\(d :: _) => True))

queryOnNA : Eff (RA [Id]@"fr") [GUARD $ FragV (sl @@ ipl) RightFragTy]
queryOnNA = queryR (Project [Id] .
                    Select (\(n :: _) => n == encrypt "mykey" "Bob"))

lFirstStrat : Eff (RA [D,Id]@"fl") [GUARD $ Plain $ [D,N,A]@@"cloud"]
                                   [GUARD $ FragV LeftFragTy RightFragTy]
lFirstStrat = do encrypt "mykey" N
                 frag "fl" "fr" [D]
                 ql <- queryOnD
                 qr <- queryOnNA
                 pure ql

main : IO ()
-- main = runTest2 (MkPEnv [D,N,A] "cloud") lFirstStrat
main = do let PCs =  [[N],[D,A]]
          genPV PCs places
          genPV PCs meetings
          genPV PCs lFirstStrat
-- main = putStrLn "lala"


-- λΠ> the (IO (LocTy $ RA [D,Id] @ "fl")) $ runInit [MkPEnv [D,N,A] "cloud" ] lFirstStrat

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
