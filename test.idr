module Main

import crypt
-- import pv
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

LeftFragTy : Loc "fl" Schema
LeftFragTy = [D, Id] @ "fl"

RightFragTy : Loc "fr" Schema
RightFragTy = [Nc, A, Id] @ "fr"

-- places : Eff (RA ([A] @ "EC2")) [GUARD $ Plain $ [D, N,  A] @ "EC2"]
--                                 [GUARD $ Plain $ [D, Nc, A] @ "EC2"]
-- places = do
--   encrypt "mykey" N
--   query (Project [A] . Select D (const True))

-- meetings : Eff (RA ([Nc] @ "EC2")) [GUARD $ Plain $ [D, Nc, A] @ "EC2"]
-- meetings = do
--   let contact = the (AES String) $ encrypt "mykey" "Bob" -- app tag
--   encrypt "mykey" N
--   query (Project [Nc] . Select Nc ((==) contact))


-- left-first strategy
-- FIXME: this should not be local but "fr". Fix the `manageIP`.
places' : Eff (RA ([Nc,A,Id] @ "local")) [GUARD $ Plain $ [D, N, A] @ "EC2"]
                                         [GUARD $ FragV LeftFragTy RightFragTy]
places' = do
  encrypt "mykey" N
  frag "fl" "fr" [D]
  -- FIXME: The selection should be available on RA
  ids <- queryL (Project [Id] . Select' D (const (ExpBool True)))
  q <- queryR (Select' Id (\i => ExpF2 (==) i (ExpRA ids)))
  pure q

-- meetings' : Eff (RA ([D, Id] @ "local")) [GUARD $ FragV LeftFragTy RightFragTy]
-- meetings' = do
--   let contact = the (AES String) $ encrypt "mykey" "Bob" -- force this
--                                                          -- to be the
--                                                          -- "app"
--                                                          -- label and
--                                                          -- also
--                                                          -- directly
--                                                          -- lift into
--                                                          -- an expr
--   ql <- queryL (id)
--   qr <- queryR (Project [Id] . Select' Nc (\n => n == (ExpAttr contact "app")))
--   pure $ Product ql qr

main : IO ()
-- main = do let PCs =  [[N],[D,A]]
--           genPV PCs (do
--             places
--             meetings)
--           genPV PCs (do
--             places'
--             meetings')
main = putStrLn "lala"

-- λΠ> the (IO (LocTy $ RA [D,Id] @ "fl")) $ runInit [MkPEnv [D,N,A] "EC2" ] lFirstStrat

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
