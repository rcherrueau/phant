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

-- Places for meetgins from the next week
-- 1
places : Eff (Expr (SCH [A]) (App,App,DB))
             [GUARD $ Plain [D,N,A]]
-- places : sch [A] from db[D,N,A]
places = do                                                      -- Alice App.Alice   (o)
  query (Project [A] . Select D nextWeek)                        -- App   App.DB      (1)

-- -- 2
meetings : Eff (Expr (SCH [D,Count]) (App,App,DB))
               [GUARD $ Plain [D,N,A]]
-- meetings : sch[D, Count] from db[D,N,A]
meetings = do                                                    -- Alice App.Alice   (2)
  query (Count [D] . Select N (ExprEq (ExprTEXT "Bob")))         -- App   App.DB      (1)

compose : Eff (Expr (SCH [A,D,Count]) (App,App,App))
              [GUARD $ Plain [D,N,A]]
compose = do                                                     -- Alice App.Alice   (o)
  q1 <- places                                                   -- App   App.DB      (1)
  q2 <- meetings                                                 -- App   App.DB      (2)
  pure (ExprProduct q1 q2)                                       -- App   App.App     (3)

-- left-first strategy
-- 3
places' : Eff (Expr (SCH [A]) (App,App,(Frag $ the (Fin 2) 1)))
              [GUARD $ Plain [D,N,A]]
              [GUARD $ FragV [[D,Id],[Nc,A,Id]]]
-- places' : sch[A] from (frags[[D, Id],[Nc,A,Id]] of db[D, N, A])
places' = do                                                     -- Alice App.Alice   (o)
  encrypt "mykey" N
  frag [[D]]
  ids  <- queryL (Project [Id] . Select D nextWeek)              -- App   App.L       (1)
  qRes <- queryR (Project [A] . Select Id (flip ExprElem ids))   -- App   App.R       (2)
  pure qRes                                                      -- App   App.R       (2)

-- -- 4
places'' : Eff (Expr (SCH [D,A]) (Alice,Alice,Alice))
               [GUARD $ Plain [D,N,A]]
               [GUARD $ FragV [[D,Id],[Nc,A,Id]]]
-- places'' : sch[D,A] from (frags[[D, Id],[Nc,A,Id]] of db[D, N, A])
places'' = do                                                    -- Alice Alice.Alice (o)
  frag [[D]]
  encrypt 1 "mykey" N
  dIds <- queryL (Project [D, Id])                               -- App   App.L       (1)
  let ids = ExprProject [Id] dIds
  qRes <- privy $ queryR (Project [A, Id] .
                          Select Id (flip ExprElem ids))         -- Alice App.R       (2)
  -- Does one of the two arguments comes from Alice place ? Yes, do
  -- the expr at alice place And keep it at alice place. Parsing the
  -- expr involve an extra send from App to Alice with dIds in
  -- arguments. It's easy to notice that since the final expr is done
  -- at Alice place but one of the expression is located at App place.
  pure (ExprProject [D,A] $ ExprProduct dIds qRes)               -- Alice Alice.Alice (3)

-- 5
meetings' : AES String -> Eff (Expr (SCH [D,Id]) (App,App,App))
                              [GUARD $ FragV [[D,Id],[Nc,A,Id]]]
-- meetings' : AES String -> sch[D,Id] from frags[[D, Id], [Nc, A, Id]]
meetings' contact = do                                           -- Alice App.Alice   (o)
  ql <- queryL (Project [D, Id])                                 -- App   App.L       (1)
  qr <- queryR (Project [Id] .
                 -- ra.Select Nc (ExprEq "Bob"))
                 -- ra.Select Nc (ExprGtEq contact))
                 Select Nc (ExprEq (ExprCRYPT contact)))         -- App   App.R       (2)
  -- Receiver of both sub expression is App so the whole expr should
  -- be done at App.
  pure (ExprProduct ql qr)                                       -- App   App.App     (3)

-- 6
meetings'' : Eff (Expr (SCH [D,A]) (Alice,Alice,Alice))
                 [GUARD $ FragV [[D,Id],[Nc,A,Id]]]
-- meetings'' : sch[D,A] from frags[[D, Id], [Nc, A, Id]]
meetings'' = do                                                  -- Alice Alice.Alice (o)
  let contact = expr.encrypt "mykey" "Bob"
  ql <- privy $ queryL (Project [D, Id])                         -- Alice App.L       (1)
  qr <- privy $ queryR (Project [A, Id] .
                        Select Nc (ExprEq contact))              -- Alice App.R       (2)
  pure (ExprProject [D,A] $ ExprProduct ql qr)                   -- Alice Alice.Alice (3)

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
