module Main

-- import pv
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

syntax "frags" [fs] = [GUARD $ FragV fs]
syntax "db" [db] = [GUARD $ Plain db]
syntax "sch" [sch] from "(" [guard] "of before" [g2] ")" = Eff (Expr (SCH sch)) g2 guard
syntax "sch" [sch] from [guard] = Eff (Expr (SCH sch)) guard

nextWeek : Expr (getU D) -> Expr BOOL
nextWeek _ = ExprBOOL True

-- Places for meetgins from the next week
places : sch [A] from db[D,N,A]
places = do
  query (Project [A] . Select D nextWeek)

meetings : sch[D, Count] from db[D,N,A]
meetings = do
  query (Count [D] . Select N (ExprEq (ExprTEXT "Bob")))

-- -- left-first strategy
places' : sch[A] from (frags[[D, Id],[Nc,A,Id]] of before db[D, N, A])
places' = do
  encrypt "mykey" N
  frag [[D]]
  ids  <- query 0 (Project [Id] . Select D nextWeek)
  qRes <- query 1 (Project [A] . Select Id (flip ExprElem ids))
  pure qRes

places'' : sch[A] from (frags[[D, Id],[Nc,A,Id]] of before db[D, N, A])
places'' = do
  frag [[D]]
  encrypt 1 "mykey" N
  dIds <- query 0 (Project [D, Id])
  let ids = ExprProject [Id] dIds
  qRes <- query 1 (Project [A] . Select Id (flip ExprElem ids))
  pure qRes

meetings' : sch[D,Id] from frags[[D, Id], [Nc, A, Id]]
meetings' = do
  ql <- query 0 (Project [D, Id])
  let contact = expr.encrypt "mykey" "Bob"
  qr <- query 1 (Project [Id] .
                 -- ra.Select Nc (ExprEq "Bob"))
                 -- ra.Select Nc (ExprGtEq contact))
                 Select Nc (ExprEq contact))
  pure (ExprProduct ql qr)

-- -- main : IO ()
-- -- -- main = do let PCs =  [[N],[D,A]]
-- -- --           genPV PCs (do
-- -- --             places
-- -- --             meetings)
-- -- --           genPV PCs (do
-- -- --             places'
-- -- --             meetings')
-- -- main = putStrLn "lala"

-- -- λPROJECT> the (IO (LocTy $ RA [D,Id] @ "fl")) $ runInit [MkPEnv [D,N,A] "EC2" ] lFirstStrat

-- -- Local Variables:
-- -- idris-load-packages: ("effects")
-- -- End:
