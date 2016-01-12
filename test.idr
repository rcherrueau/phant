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


-- syntax fromFrag [fs] fromDB [db] = [GUARD $ Plain db][GUARD $ FragV fs]
-- syntax fromFrag [db] = [GUARD $ FragV db]
-- syntax "Frag" [fs] "before" [next] = [next] [GUARD $ FragV fs]
-- syntax from [db1] [next] = [next] db1
-- syntax from [db] = db
syntax [sch] "{"[x]"}" [guard1] "before" [guard2] = Eff (Expr (SCH sch) {ctx=x}) guard2 guard1
syntax [sch] "{"[x]"}" [guard] = Eff (Expr (SCH sch) {ctx=x}) guard

syntax "frags" [fs] = [GUARD $ FragV fs]
-- syntax "frags" [fs] [next] = next [GUARD $ FragV fs]
syntax "db" [db] = [GUARD $ Plain db]
 --
-- syntax [sch] "{"[x]"}" "fromFrag" [fs]  = Eff (Expr (SCH sch) {ctx=x}) [GUARD $ FragV fs]

-- syntax from "(" [F1] "," [F2] ")" before [DB]                   =
--   Eff () [GUARD $ Plain DB] [GUARD $ FragV F1 F2]
-- syntax [sch] from "(" [F1] "," [F2] ") from" [DB]             =
--   Eff (Expr (SCH sch)) [GUARD $ Plain DB] [GUARD $ FragV F1 F2]

nextWeek : Expr (getU D) {ctx=[D]} -> Expr BOOL {ctx=[]}
nextWeek _ = ExprBOOL True

-- Places for meetgins from the next week
places : [A] {[A]} db[D,N,A]
places = do
  query (Project [A] . Select D nextWeek)

meetings : [D, Count] {[D]} db[D,N,A]
meetings = do
  query (Count [D] . Select N (ExprEq (ExprTEXT "Bob")))

-- left-first strategy
places' : Eff (Expr (SCH [A]) {ctx=[A]}) [GUARD $ Plain [D, N, A]]
                                         [GUARD $ FragV [[D, Id],[Nc,A,Id]]]
places' = do
  encrypt "mykey" N
  frag [[D]]
  ids  <- query 0 (Project [Id] . Select D nextWeek)
  qRes <- query 1 (Project [A] . Select Id (flip ExprElem ids))
  pure qRes

places'' : Eff (Expr (SCH [A]) {ctx=[A,D]}) [GUARD $ Plain [D, N, A]]
                                            [GUARD $ FragV [[D, Id],[Nc, A, Id]]]
places'' = do
  frag [[D]]
  encrypt 1 "mykey" N
  dIds <- query 0 (Project [D, Id])
  let ids = ExprProject [Id] dIds
  qRes <- query 1 (Project [A] . Select Id (flip ExprElem ids))
  pure qRes

meetings' : [D,Id] {[D,Id]} frags[[D, Id], [Nc, A, Id]]
meetings' = do
  ql <- query 0 (Project [D, Id])
  let contact = expr.encrypt "mykey" "Bob"
  qr <- query 1 (Project [Id] .
                 -- ra.Select Nc (ExprEq "Bob"))
                 -- ra.Select Nc (ExprGtEq contact))
                 Select Nc (ExprEq contact))
  pure (ExprProduct ql qr)

-- main : IO ()
-- -- main = do let PCs =  [[N],[D,A]]
-- --           genPV PCs (do
-- --             places
-- --             meetings)
-- --           genPV PCs (do
-- --             places'
-- --             meetings')
-- main = putStrLn "lala"

-- λPROJECT> the (IO (LocTy $ RA [D,Id] @ "fl")) $ runInit [MkPEnv [D,N,A] "EC2" ] lFirstStrat

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:

