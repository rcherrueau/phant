module phant.test

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

syntax GUARD [x] [y] [z] = {bjn : Vect n U} -> Guard x y bjn (Expr z bjn)
syntax FRAG [x] = (FragV x)
syntax DB [x] = (Plain x)

-- nextWeek : Expr (getU D) p -> Expr BOOL AppP
-- nextWeek _ = ExprBOOL True
nextWeek : {bjn : Vect n U} -> Expr (getU D) bjn -> Expr BOOL bjn
nextWeek _ = ExprBOOL True

-- -- 1
-- places : Eff (Expr (SCH [A]) (App,App,DB))
--              [GUARD $ Plain [D,N,A]]
-- places = do                                                      -- Alice App.Alice   (o)
--   query (Project [A] . Select D nextWeek)                        -- App   App.DB      (1)
-- places : Guard (Plain [D,N,A]) (Plain [D,N,A]) Nil (Expr (SCH [A]) Nil)
places : GUARD (DB[D,N,A]) (DB[D,N,A]) (SCH [A])
places = Query (Project [A] . Select D nextWeek)


-- -- 2
-- meetings : Eff (Expr (SCH [D,Count]) (App,App,DB))
--                [GUARD $ Plain [D,N,A]]
-- meetings = do                                                    -- Alice App.Alice   (2)
--   query (Count [D] . Select N (ExprEq (ExprTEXT "Bob")))         -- App   App.DB      (1)
-- meetings : Guard (Plain [D,N,A]) (Plain [D,N,A]) Nil (Expr (SCH [D,Count]) Nil)
meetings : GUARD (DB[D,N,A]) (DB[D,N,A]) (SCH [D,Count])
meetings = Query (Count [D] . Select N (ExprEq (ExprTEXT "Bob")))


-- -- -- 1 & 2
-- compose : Eff (Expr (SCH [A,D,Count]) (App,App,App))
--               [GUARD $ Plain [D,N,A]]
-- compose = do                                                     -- Alice App.Alice   (o)
--   q1 <- places                                                   -- App   App.DB      (1)
--   q2 <- meetings                                                 -- App   App.DB      (2)
--   pure (ExprProduct q1 q2)                                       -- App   App.App     (3)
-- compose : Guard (Plain [D,N,A]) (Plain [D,N,A]) Nil (Expr (SCH [A,D,Count]) Nil)
compose : GUARD (DB[D,N,A]) (DB[D,N,A]) (SCH [A,D,Count])
compose = places >>= \q1 =>
          meetings >>= \q2 =>
          Pure (ExprProduct q1 q2)

-- composeDo : Guard (Plain [D,N,A]) (Plain [D,N,A]) (Expr Nil (SCH [A,D,Count]))
composeDo : GUARD (DB[D,N,A]) (DB[D,N,A]) (SCH [A,D,Count])
composeDo = do
  q1 <- places
  q2 <- meetings
  pure (ExprProduct q1 q2)


-- -- left-first strategy
-- -- 3
-- places' : Eff (Expr (SCH [A]) (App,App,(Frag $ the (Fin 2) 1)))
--               [GUARD $ Plain [D,N,A]]
--               [GUARD $ FragV [[D,Id],[Nc,A,Id]]]
-- -- places' : sch[A] from (frags[[D, Id],[Nc,A,Id]] of db[D, N, A])
-- places' = do                                                     -- Alice App.Alice   (o)
--   encrypt "mykey" N
--   frag [[D]]
--   ids  <- queryL (Project [Id] . Select D nextWeek)              -- App   App.L       (1)
--   qRes <- queryR (Project [A] . Select Id (flip ExprElem ids))   -- App   App.R       (2)
--   pure qRes                                                      -- App   App.R       (2)
-- placesF : Guard (Plain [D,N,A]) (FragV [[D,Id], [Nc,A,Id]]) (Expr Nil (SCH [A]))
placesF : GUARD (DB[D,N,A]) (FRAG[[D,Id], [Nc,A,Id]]) (SCH [A])
placesF = Encrypt "mykey" N                                      >>= \_ =>
          Frag [[D]]                                             >>= \_ =>
          QueryF 0 (Project [Id] . Select D nextWeek)            >>= \ids =>
          QueryF 1 (Project [A] . Select Id (flip ExprElem ids)) >>= \res =>
          Pure res

-- placesFDo : Guard (Plain [D,N,A]) (FragV [[D,Id], [Nc,A,Id]]) (Expr Nil (SCH [A]))
placesFDo : GUARD (DB[D,N,A]) (FRAG[[D,Id], [Nc,A,Id]]) (SCH [A])
placesFDo = do
  Encrypt "mykey" N
  Frag [[D]]
  ids <- QueryF 0 (Project [Id] . Select D nextWeek)
  res <- QueryF 1 (Project [A] . Select Id (flip ExprElem ids))
  pure res


-- -- 4
-- places'' : Eff (Expr (SCH [D,A]) (Alice,Alice,Alice))
--                [GUARD $ Plain [D,N,A]]
--                [GUARD $ FragV [[D,Id],[Nc,A,Id]]]
-- -- places'' : sch[D,A] from (frags[[D, Id],[Nc,A,Id]] of db[D, N, A])
-- places'' = do                                                    -- Alice Alice.Alice (o)
--   frag [[D]]
--   encrypt 1 "mykey" N
--   dIds <- queryL (Project [D, Id])                               -- App   App.L       (1)
--   let ids = ExprProject [Id] dIds
--   qRes <- privy $ queryR (Project [A, Id] .
--                           Select Id (flip ExprElem ids))         -- Alice App.R       (2)
--   -- Does one of the two arguments comes from Alice place ? Yes, do
--   -- the expr at alice place And keep it at alice place. Parsing the
--   -- expr involve an extra send from App to Alice with dIds in
--   -- arguments. It's easy to notice that since the final expr is done
--   -- at Alice place but one of the expression is located at App place.
--   pure (ExprProject [D,A] $ ExprProduct dIds qRes)               -- Alice Alice.Alice (3)
-- placesF' : Guard (Plain [D,N,A]) (FragV [[D,Id], [Nc,A,Id]]) (Expr Nil (SCH [D,A]))
-- placesF' = Encrypt "mykey" N                                      >>= \_ =>
--            Frag [[D]]                                             >>= \_ =>
--            QueryF 0 (Project [D, Id] . Select D nextWeek)         >>= \dIds =>
--            Let (ExprProject [Id] dIds) (
--              QueryF 1 (Project [A] . Select Id (flip ExprElem (ExprSCH [Id]))) >>= \res =>
--              Pure (ExprProject [D,A] $ ExprProduct dIds res))


-- placesFDo' : {bjn : Vect n U} -> Guard (Plain [D,N,A]) (FragV [[D,Id], [Nc,A,Id]]) bjn (Expr (SCH [D,A]))
placesFDo' : GUARD (DB[D,N,A]) (FRAG[[D,Id], [Nc,A,Id]]) (SCH [D,A])
placesFDo' =  do
  Encrypt "mykey" N
  Frag [[D]]
  dIds <- QueryF 0 (Project [D, Id] . Select D nextWeek)
  Let (ExprProject [Id] dIds) (do
    res <- QueryF 1 (Project [A] . Select Id (flip ExprElem (var Stop)))
    pure (ExprProject [D,A] $ ExprProduct dIds res))


-- placesFDo'' : Guard (Plain [D,N,A]) (FragV [[D,Id], [Nc,A,Id]]) Nil (Expr (SCH [D,A]))
placesFDo'' : GUARD (DB[D,N,A]) (FRAG[[D,Id], [Nc,A,Id]]) (SCH [D,A])
placesFDo'' =  guard(do
  Encrypt "mykey" N
  Frag [[D]]
  dIds <- QueryF 0 (Project [D, Id] . Select D nextWeek)
  let ids = ExprProject [Id] dIds
  res <- QueryF 1 (Project [A] . Select Id (flip ExprElem ids))
  pure (ExprProject [D,A] $ ExprProduct dIds res))

-- -- 5
-- meetings' : AES String -> Eff (Expr (SCH [D,Id]) (App,App,App))
--                               [GUARD $ FragV [[D,Id],[Nc,A,Id]]]
-- -- meetings' : AES String -> sch[D,Id] from frags[[D, Id], [Nc, A, Id]]
-- meetings' contact = do                                           -- Alice App.Alice   (o)
--   ql <- queryL (Project [D, Id])                                 -- App   App.L       (1)
--   qr <- queryR (Project [Id] .
--                  -- ra.Select Nc (ExprEq "Bob"))
--                  -- ra.Select Nc (ExprGtEq contact))
--                  Select Nc (ExprEq (ExprCRYPT contact)))         -- App   App.R       (2)
--   -- Receiver of both sub expression is App so the whole expr should
--   -- be done at App.
--   pure (ExprProduct ql qr)                                       -- App   App.App     (3)
-- meetingF : AES String -> Guard (FragV [[D,Id], [Nc,A,Id]])
--                                (FragV [[D,Id], [Nc,A,Id]])
--                                (Expr Nil (SCH [D,Id]))
meetingF : AES String -> GUARD (FRAG[[D,Id], [Nc,A,Id]]) (FRAG[[D,Id], [Nc,A,Id]]) (SCH [D,Id])
meetingF c = QueryF 0 (Project [D, Id])                                 >>= \ql =>
             QueryF 1 (Project [Id] .
                       Select Nc (ExprEq (ExprCRYPT c)))                >>= \qr =>
             Pure (ExprProduct ql qr)

-- -- -- 6
-- -- meetings'' : Eff (Expr (SCH [D,A]) (Alice,Alice,Alice))
-- --                  [GUARD $ FragV [[D,Id],[Nc,A,Id]]]
-- -- -- meetings'' : sch[D,A] from frags[[D, Id], [Nc, A, Id]]
-- -- meetings'' = do                                                  -- Alice Alice.Alice (o)
-- --   let contact = expr.encrypt "mykey" "Bob"
-- --   ql <- privy $ queryL (Project [D, Id])                         -- Alice App.L       (1)
-- --   qr <- privy $ queryR (Project [A, Id] .
-- --                         Select Nc (ExprEq contact))              -- Alice App.R       (2)
-- --   pure (ExprProject [D,A] $ ExprProduct ql qr)                   -- Alice Alice.Alice (3)
-- meetingF' : AES String -> Guard (FragV [[D,Id], [Nc,A,Id]])
--                                 (FragV [[D,Id], [Nc,A,Id]])
--                                 (Expr (SCH [D, A]))
-- meetingF' c = Privy <*> QueryF 0 (Project [D, Id]) >>= \ql =>
--               Privy <*> QueryF 1 (Project [A, Id] .
--                                   Select Nc (ExprEq (ExprCRYPT c))) >>= \qr =>
--               Pure (ExprProject [D,A] $ ExprProduct ql qr)


-- -- main : IO ()
-- -- main = -- do let PCs =  [[N],[D,A]]
-- --           -- genPV PCs (do
-- --           --   places
-- --           --   meetings)
-- --           genPV (do
-- --             places'
-- --             meetings'')
-- -- -- -- main = putStrLn "lala"

-- -- -- λPROJECT> the (IO (LocTy $ RA [D,Id] @ "fl")) $ runInit [MkPEnv [D,N,A] "EC2" ] lFirstStrat

-- -- -- Local Variables:
-- -- -- idris-load-packages: ("effects")
-- -- -- End:
