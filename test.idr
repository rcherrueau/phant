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
LeftFragTy = [D, Id] @@ "fl"

RightFragTy : Schema @ "fr"
RightFragTy = [Nc, A, Id] @@ "fr"

places : Eff (RA [A] @ "cloud") [GUARD $ Plain $ [D, Nc, A] @@ "cloud"]
places = do
  encrypt "mykey" N
  query (Project [A] . Select D (const True))

meetings : Eff (RA [Nc] @ "cloud") [GUARD $ Plain $ [D, Nc, A] @@ "cloud"]
meetings = do
  let contact = the (AES String) $ encrypt "mykey" "Bob"
  encrypt "mykey" N
  query (Project [Nc] . Select Nc ((==) contact))

-- left-first strategy
places' : Eff (RA [A] @ "fr") [GUARD $ Plain $ [D, N, A] @@ "cloud"]
                              [GUARD $ FragV LeftFragTy RightFragTy]
places' = do
  encrypt "mykey" N
  frag "fl" "fr" [D]
  -- FIXME: The selection should be available on RA
  ids <- queryL (Project [Id] . Select D (const True))
  q   <- queryR (Project [A] . Select Id ((==) 1))
  pure q

meetings' : Eff (RA [D, Id] @ "local") [GUARD $ FragV LeftFragTy RightFragTy]
meetings' = do
  let contact = the (AES String) $ encrypt "mykey" "Bob"
  ql <- queryL (id)
  qr <- queryR (Project [Id] . Select Nc ((==) contact))
  pure $ Product ql qr

main : IO ()
main = do let PCs =  [[N],[D,A]]
          genPV PCs (do
            places
            meetings)
          genPV PCs (do
            places'
            meetings')
-- main = putStrLn "lala"


-- λΠ> the (IO (LocTy $ RA [D,Id] @ "fl")) $ runInit [MkPEnv [D,N,A] "cloud" ] lFirstStrat

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
