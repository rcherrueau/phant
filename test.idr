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

LeftFragTy : Loc "fl" Schema
LeftFragTy = [D, Id] @ "fl"

RightFragTy : Loc "fr" Schema
RightFragTy = [Nc, A, Id] @ "fr"

places : Eff (Loc "EC2" (DB $ liftSch [A]))
             [GUARD $ Plain $ [D, N,  A] @ "EC2"]
             [GUARD $ Plain $ [D, Nc, A] @ "EC2"]
places = do
  encrypt "mykey" N
  query (Project [A] . Select D (liftLoc2 const (True @ "app")))

meetings : Eff (Loc "EC2" (DB $ liftSch [Nc]))
               [GUARD $ Plain $ [D, Nc, A] @ "EC2"]
meetings = do
  let contact = the (AES String) $ encrypt "mykey" "Bob" -- app tag
  encrypt "mykey" N
  query (Project [Nc] . Select Nc (liftLoc2 (==) (contact @ "app")))

-- left-first strategy
-- FIXME: this should not be local but "fr". Fix the `manageIP`.
places' : Eff (Loc "local" (DB $ liftSch [Nc,A,Id]))
              [GUARD $ Plain $ [D, N, A] @ "EC2"]
              [GUARD $ FragV LeftFragTy RightFragTy]
places' = do
  encrypt "mykey" N
  frag "fl" "fr" [D]
  ids <- queryL (Project [Id] . Select D (liftLoc2 const (True @ "app")))
  q   <- queryR (Select Id (\i => liftLoc2 (elem) i ids))
  pure q

meetings' : Eff (Loc "fr" (DB $ liftSch [Id]))
                [GUARD $ FragV LeftFragTy RightFragTy]
meetings' = do
  let contact = the (AES String) $ encrypt "mykey" "Bob"
  ql <- queryL (id)
  qr <- queryR (Project [Id] .
                -- Select Nc (liftLoc2 (==) ("Bob" @ "app")))
                -- Select Nc (liftLoc2 (>=) (contact @ "app")))
                Select Nc (liftLoc2 (==) (contact @ "app")))
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
