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

nextWeek : Expr ((getU D) @@ ip) -> Expr (BOOL @@ App)
nextWeek d = ExprBOOL True

------------------------------------------------------------------------------------
-- Note: put myPCs at []
------------------------------------------------------------------------------------

-- -- -- Places for meetgins of the next week
-- places : Eff (Expr $ SCH [A] @@ "EC2") [GUARD $ Plain $ [D, N, A] @@ "EC2"]
-- places = do
--   query (project [A] . select D nextWeek)

-- -- Places for meetgins of the next week
-- placesDA : Eff (Expr $ SCH [D, A] @@ "EC2") [GUARD $ Plain $ [D, N, A] @@ "EC2"]
-- placesDA = do
--   query (project [D, A] . select D nextWeek)

-- meetings : Eff (Expr $ SCH [D, Count] @@ "EC2") [GUARD $ Plain $ [D, N, A] @@ "EC2"]
-- meetings = do
--   query (count [D] . select N ((==) "Bob"))

------------------------------------------------------------------------------------
-- Note: put myPCs at [[N],[D,A]]
------------------------------------------------------------------------------------

-- -- left-first strategy
-- places' : Eff (Expr $ SCH [A] @@ "fr")
--           [GUARD $ Plain $ [D, N, A] @@ "EC2"]
--           -- [GUARD $ Plain $ [D, Nc, A] @@ "EC2"]
--           [GUARD $ FragV ([D, Id] @@ "fl") ([Nc, A, Id] @@ "fr")]
-- places' = do
--   encrypt "mykey" N
--   frag [D] "fl" "fr"
--   ids  <- queryL (project [Id] . select D nextWeek)
--   qRes <- queryR (project [A] . select Id (flip elem ids))
--   pure qRes

-- -- normal strategy
-- places' : Eff (Expr $ SCH [D, A] @@ Local)
--           [GUARD $ Plain $ [D, N, A] @@ "EC2"]
--           -- [GUARD $ Plain $ [D, Nc, A] @@ "EC2"]
--           [GUARD $ FragV ([D, Id] @@ "fl") ([Nc, A, Id] @@ "fr")]
-- places' = do
--   encrypt "mykey" N
--   frag [D] "fl" "fr"
--   dIds <- queryL (project [D, Id] . select D nextWeek) -- [D,Id] @@ "fr"
--   let ids = project [Id] dIds  -- actual solution: avoid project at Expr level
--   qRes <- queryR (select Id (flip elem ids)) -- I need a context on
--                                              -- select to knows where
--                                              -- the id comes from. If
--                                              -- it comes from a [D,id]
--                                              -- then put tag at Local.
--   pure ?hole

meetings' : Eff (Expr $ SCH [D,Count] @@ App) [GUARD $ FragV ([D, Id] @@ "fl")
                                                             ([Nc, A, Id] @@ "fr")]
meetings' = do
  let contact = expr.encrypt "mykey" "Bob"
  ql <- queryL (id) -- [D,Id] @@ "fl"
  qr <- queryR (project [Id] .
                -- ra.select Nc (expr.(==) "Bob"))
                -- ra.select Nc (expr.(>=) contact))
                select Nc ((==) contact)) -- [Id] @@ "fr"
  -- pure (count [D] $ (ql * qr))
  pure (count [D] $ (ql * qr))

main : IO ()
-- main = do let PCs =  [[N],[D,A]]
--           genPV PCs (do
--             places
--             meetings)
--           genPV PCs (do
--             places'
--             meetings')
main = putStrLn "lala"

-- λPROJECT> the (IO (LocTy $ RA [D,Id] @ "fl")) $ runInit [MkPEnv [D,N,A] "EC2" ] lFirstStrat

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
