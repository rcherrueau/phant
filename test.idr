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

LeftFragTy : Schema
LeftFragTy = [D, Id]

RightFragTy : Schema
RightFragTy = [Nc, A, Id]

places : Eff (DB $ liftSch [A]) [GUARD $ Plain [D, N,  A]]
                                [GUARD $ Plain [D, Nc, A]]
places = do
  encrypt "mykey" N
  query (Project [A] . Select D (const True))

meetings : Eff (DB $ liftSch [Nc]) [GUARD $ Plain [D, Nc, A]]
meetings = do
  let contact = the (AES String) $ encrypt "mykey" "Bob" -- app tag
  encrypt "mykey" N
  query (Project [Nc] . Select Nc ((==) contact))

-- left-first strategy
-- FIXME: this should not be local but "fr". Fix the `manageIP`.
places' : Eff (DB $ liftSch [Nc,A,Id])
              [GUARD $ Plain [D, N, A]]
              [GUARD $ FragV LeftFragTy RightFragTy]
places' = do
  encrypt "mykey" N
  frag [D]
  ids <- queryL (Project [Id] . Select D (const True))
  q   <- queryR (Select Id (\i => elem i ids))
  pure q

meetings' : Eff (DB $ liftSch [Id])
                [GUARD $ FragV LeftFragTy RightFragTy]
meetings' = do
  let contact = the (AES String) $ encrypt "mykey" "Bob"
  ql <- queryL (id)
  qr <- queryR (Project [Id] .
                -- Select Nc (liftLoc2 (==) ("Bob" @ "app")))
                -- Select Nc (liftLoc2 (>=) (contact @ "app")))
                Select Nc ((==) contact))
  pure qr

main : IO ()
main = do let PCs =  [[N],[D,A]]
          genPV PCs (do
            places
            meetings)
          genPV PCs (do
            places'
            meetings')
-- main = putStrLn "lala"

-- λΠ> the (IO (LocTy $ RA [D,Id] @ "fl")) $ runInit [MkPEnv [D,N,A] "EC2" ] lFirstStrat

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
