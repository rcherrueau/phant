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

places : Eff (Expr ((liftSchU [A]) @ "EC2")) [GUARD $ Plain $ [D, N,  A] @ "EC2"]
                                             [GUARD $ Plain $ [D, Nc, A] @ "EC2"]
places = do
  encrypt "mykey" N
  query (Project [A] . Select' D (ra.const (ExpBool True)))

meetings : Eff (Expr ((liftSchU [Nc]) @ "EC2")) [GUARD $ Plain $ [D, Nc, A] @ "EC2"]
meetings = do
  let contact = the (AES String) $ encrypt "mykey" "Bob" -- app tag
  encrypt "mykey" N
  query (Project [Nc] . Select Nc ((==) contact))


-- left-first strategy
-- FIXME: this should not be local but "fr". Fix the `manageIP`.
places' : Eff (Expr ((liftSchU [Nc,A,Id]) @ "local"))
              [GUARD $ Plain $ [D, N, A] @ "EC2"]
              [GUARD $ FragV LeftFragTy RightFragTy]
places' = do
  encrypt "mykey" N
  frag "fl" "fr" [D]
  ids <- queryL (Project [Id] . Select' D (ra.const (ExpBool True)))
  q   <- queryR (Select' Id (\i => liftExpr2 (==) i ids))
  pure q

meetings' : Eff (Expr ((liftSchU [D,Id]) @ ?local))
            [GUARD $ FragV LeftFragTy RightFragTy]
meetings' = do
  let contact = the (AES String) $ encrypt "mykey" "Bob"
  ql <- queryL (id)
  qr <- queryR (Project [Id] . Select' Nc (liftExpr2 (==) (ExpAES contact {u=(TEXT 255)})))
  pure $ liftExpr2 (*) ql qr

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
