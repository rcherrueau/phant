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

nextWeek : Expr (getU D) [D] -> Expr BOOL []
nextWeek _ = ExprBOOL True

-- Places for meetgins of the next week
places : Eff (Expr (SCH [A]) [A]) [GUARD $ Plain [D, N, A]]
places = do
  query (Project [A] . Select D nextWeek)

meetings : Eff (Expr (SCH [D, Count]) [D]) [GUARD $ Plain [D, N, A]]
meetings = do
  query (Count [D] . Select N (ExprEq (ExprTEXT "Bob")))

-- left-first strategy
places' : Eff (Expr (SCH [A]) [A]) [GUARD $ Plain [D, N, A]]
                                   [GUARD $ FragV [D, Id] [Nc, A, Id]]
places' = do
  encrypt "mykey" N
  frag [D]
  ids  <- queryL (Project [Id] . Select D nextWeek)
  qRes <- queryR (Project [A] . Select Id (flip ExprElem ids))
  pure qRes

places'' : Eff (Expr (SCH [A]) [A,D]) [GUARD $ Plain [D, N, A]]
                                      [GUARD $ FragV [D, Id] [Nc, A, Id]]
places'' = do
  encrypt "mykey" N
  frag [D]
  dIds  <- queryL (Select D nextWeek)
  let ids = ExprProject [Id] dIds
  qRes <- queryR (Project [A] . Select Id (flip ExprElem ids))
  pure qRes

-- meetings' : Eff (Expr $ SCH [D,Count]) [GUARD $ FragV [D, Id] [Nc, A, Id]]
-- meetings' = do
--   let contact = expr.encrypt "mykey" "Bob"
--   ql <- queryL (id)
--   qr <- queryR (project [Id] .
--                 -- ra.select Nc (expr.(==) "Bob"))
--                 -- ra.select Nc (expr.(>=) contact))
--                 select Nc ((==) contact))
--   pure (count [D] $ (ql * qr))

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

