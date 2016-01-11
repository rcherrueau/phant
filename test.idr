module Main

import pv
import crypt
import guard

D : Attribute
D = ("Date", NAT)

N : Attribute
N = ("Name", TEXT)

Nc : Attribute
Nc = ("Name", CRYPT TEXT)

A : Attribute
A = ("Addr", TEXT)

LeftFragTy : Schema
LeftFragTy = [D, Id]

RightFragTy : Schema
RightFragTy = [Nc, A, Id]

nextWeek : Expr (getU D) -> Expr BOOL
nextWeek d = ExprBOOL True

-- Places for meetgins of the next week
places : Eff (Expr $ SCH [A]) [GUARD $ Plain [D, N, A]]
places = do
  query (π [A] . σ D nextWeek)

meetings : Eff (Expr $ SCH [D, Count]) [GUARD $ Plain [D, N, A]]
meetings = do
  query (count [D] . σ N ((==) "Bob"))

-- left-first strategy
places' : Eff (Expr $ SCH [A]) [GUARD $ Plain [D, N, A]]
                               [GUARD $ FragV LeftFragTy RightFragTy]
places' = do
  encrypt "mykey" N
  frag [D]
  ids  <- queryL (π [Id] . σ D nextWeek)
  let ra = queryR (π [A] . σ Id (flip elem ids))
  qRes <- ra
  pure qRes

meetings' : Eff (Expr $ SCH [D,Count])
                [GUARD $ FragV LeftFragTy RightFragTy]
meetings' = do
  let contact = expr.encrypt "mykey" "Bob"
  ql <- queryL (id)
  qr <- queryR (π [Id] .
                -- ra.σ Nc (expr.(==) "Bob"))
                -- ra.σ Nc (expr.(>=) contact))
                σ Nc ((==) contact))
  pure (count [D] $ (ql * qr))

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
