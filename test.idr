module Main

import pv
import crypt
import guard

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

places : Eff (Expr $ SCH [Nc]) [GUARD $ Plain [D, N,  A]]
                               [GUARD $ Plain [D, Nc, A]]
places = do
  encrypt "mykey" N
  query (π [Nc] . σ D (\d => d == Z))

meetings : Eff (Expr $ SCH [Nc]) [GUARD $ Plain [D, Nc, A]]
meetings = do
  encrypt "mykey" N
  query (π [Nc] . σ Nc ((==) (encrypt "mykey" "Bob")))

-- left-first strategy
places' : Eff (Expr $ SCH [Nc,A,Id]) [GUARD $ Plain [D, N, A]]
                                     [GUARD $ FragV LeftFragTy RightFragTy]
places' = do
  encrypt "mykey" N
  frag [D]
  ids  <- queryL (π [Id] . σ D ((==) (S Z)))
  let q = queryR (σ Id (flip elem ids))
  qRes <- q
  pure qRes

meetings' : Eff (Expr $ SCH [D,Id])
                [GUARD $ FragV LeftFragTy RightFragTy]
meetings' = do
  let contact = expr.encrypt "mykey" "Bob"
  ql <- queryL (id)
  qr <- queryR (π [Id] .
                -- ra.σ Nc (expr.(==) "Bob"))
                -- ra.σ Nc (expr.(>=) contact))
                σ Nc ((==) contact))
  pure (ql * qr)

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
