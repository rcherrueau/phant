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
-- 1
places : sch [A] from db[D,N,A]                          -- 0 App.Alice   (2)
places = do
  query (Project [A] . Select D nextWeek)                -- App App.DB    (1)

-- 2
meetings : sch[D, Count] from db[D,N,A]                  -- 0   App.Alice (2)
meetings = do
  query (Count [D] . Select N (ExprEq (ExprTEXT "Bob"))) -- App App.DB    (1)

-- left-first strategy
-- 3
places' : sch[A] from (frags[[D, Id],[Nc,A,Id]] of before db[D, N, A])
places' = do
  encrypt "mykey" N
  frag [[D]]
  ids  <- queryL (Project [Id] . Select D nextWeek)               -- App App.L     (1)
  qRes <- queryR (Project [A] . Select Id (flip ExprElem ids))    -- App App.R     (2)
  pure qRes                                                       -- 0   App.Alice (3)

-- 4
places'' : sch[D,A] from (frags[[D, Id],[Nc,A,Id]] of before db[D, N, A])
places'' = do
  frag [[D]]
  encrypt 1 "mykey" N
  dIds <- queryL (Project [D, Id])                                 -- App   App.L   (1)
  let ids = ExprProject [Id] dIds
  qRes <- queryR (Project [A, Id] . Select Id (flip ExprElem ids)) -- Alice App.R   (2)
  pure (ExprProject [D,A] $ ExprProduct dIds qRes)                 -- 0 App.Alice / 0 Alice.0 (3)

-- 5
meetings' : sch[D,Id] from frags[[D, Id], [Nc, A, Id]]
meetings' = do
  let contact = expr.encrypt "mykey" "Bob"
  ql <- queryL (Project [D, Id])                                   -- App   App.L (1a)
  qr <- queryR (Project [Id] .                                     -- App   App.R (1b)
                 -- ra.Select Nc (ExprEq "Bob"))
                 -- ra.Select Nc (ExprGtEq contact))
                 Select Nc (ExprEq contact))
  pure (ExprProduct ql qr)                                         -- 0     App.Alice (2)

-- 6
meetings'' : sch[D,A] from frags[[D, Id], [Nc, A, Id]]
meetings'' = do
  ql <- queryL (Project [D, Id])                                   -- Alice App.L   (1)
  let contact = expr.encrypt "mykey" "Bob"
  qr <- queryR (Project [A, Id] . Select Nc (ExprEq contact))      -- Alice App.R   (2)
  pure (ExprProject [D,A] $ ExprProduct ql qr)                     -- 0     Alice.0 (3)
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
