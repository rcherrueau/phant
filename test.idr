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
syntax "sch" [sch] from "(" [guard] "of" [g2] ")" = Eff (Expr (SCH sch)) g2 guard
syntax "sch" [sch] from [guard] = Eff (Expr (SCH sch)) guard

nextWeek : Expr (getU D) p -> Expr BOOL AppP
nextWeek _ = ExprBOOL True

-- -- Places for meetgins from the next week
-- -- 1
-- places : Eff (Expr (SCH [A])) [GUARD $ Plain [D,N,A]]    -- 0 App.Alice   (2)
-- -- places : sch [A] from db[D,N,A]
-- places = do
--   query (Project [A] . Select D nextWeek)                -- App App.DB    (1)

-- -- 2
-- meetings : Eff (Expr (SCH [D,Count])) [GUARD $ Plain [D,N,A]]
-- -- meetings : sch[D, Count] from db[D,N,A]                  -- 0   App.Alice (2)
-- meetings = do
--   query (Count [D] . Select N (ExprEq (ExprTEXT "Bob"))) -- App App.DB    (1)

-- -- left-first strategy
-- -- 3
-- places' : Eff (Expr (SCH [A])) [GUARD $ Plain [D,N,A]]
--                                [GUARD $ FragV [[D,Id],[Nc,A,Id]]]
-- -- places' : sch[A] from (frags[[D, Id],[Nc,A,Id]] of db[D, N, A])
-- places' = do
--   encrypt "mykey" N
--   frag [[D]]
--   ids  <- queryL (Project [Id] . Select D nextWeek)               -- App App.L     (1)
--   qRes <- queryR (Project [A] . Select Id (flip ExprElem ids))    -- App App.R     (2)
--   pure qRes                                                       -- 0   App.Alice (3)

-- -- 4
-- places'' : Eff (Expr (SCH [D,A])) [GUARD $ Plain [D,N,A]]
--                                   [GUARD $ FragV [[D,Id],[Nc,A,Id]]]
-- -- places'' : sch[D,A] from (frags[[D, Id],[Nc,A,Id]] of db[D, N, A])
-- places'' = do
--   frag [[D]]
--   encrypt 1 "mykey" N
--   dIds <- queryL (Project [D, Id])                                 -- App   App.L   (1)
--   let ids = ExprProject [Id] dIds
--   qRes <- queryR (Project [A, Id] . Select Id (flip ExprElem ids)) -- Alice App.R   (2)
--   pure (ExprProject [D,A] $ ExprProduct dIds qRes)                 -- 0 App.Alice / 0 Alice.0 (3)

-- -- 5
-- meetings' : AES String -> Eff (Expr (SCH [D,Id]))
--                               [GUARD $ FragV [[D,Id],[Nc,A,Id]]]
-- -- meetings' : AES String -> sch[D,Id] from frags[[D, Id], [Nc, A, Id]]
-- meetings' contact = do
--   ql <- queryL (Project [D, Id])                                   -- App   App.L (1a)
--   qr <- queryR (Project [Id] .                                     -- App   App.R (1b)
--                  -- ra.Select Nc (ExprEq "Bob"))
--                  -- ra.Select Nc (ExprGtEq contact))
--                  Select Nc (ExprEq (ExprCRYPT contact)))
--   pure (ExprProduct ql qr)                                         -- 0     App.Alice (2)

-- 6
meetings'' : Eff (Expr (SCH [D,A]) (Alice,App,App))
                  [GUARD $ FragV [[D,Id],[Nc,A,Id]]]
-- meetings'' : sch[D,A] from frags[[D, Id], [Nc, A, Id]]
meetings'' = do
  ql <- backTo Alice $ queryL (Project [D, Id])                    -- Alice App.L   (1)
  let contact = expr.encrypt "mykey" "Bob"
  qr <- backTo Alice $ queryR (Project [A, Id] .
                               Select Nc (ExprEq contact))         -- Alice App.R   (2)
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
