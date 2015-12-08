module phant.sql

import psql

%default total
%hide List.intersect

data Sch : Schema -> Type where
  MkSch : (s : Schema) -> Sch s

Id : Attribute
Id = ("Id", NAT)

join : (s1 : Schema) -> (s2 : Schema) -> {auto pS1 : NonEmpty s1} -> {auto pS2 : NonEmpty s2} -> Schema
join [] ys {pS1=IsNonEmpty} impossible
join xs [] {pS2=IsNonEmpty} impossible
join (id :: s1) s2 = joinR s1 (tail s2)
  where
  joinR : Schema -> Schema -> Schema
  joinR []        ys = ys
  joinR (x :: xs) ys = x :: (joinR xs ys)

-- Our language
-- st1 is the type of the state before the computation
-- st2 is the type of the state after the computation
-- a is the rest of the computation
data Term : (st1 : Type) -> (st2 : Type) -> a -> Type where
  Frag   : (s1 : Schema) -> a -> Term (Sch s2) (Sch $ Id :: (intersect s1 s2), Sch $ Id :: (s2 \\ s1)) a
  Query  : (q : RA s1 -> RA s3) -> a -> Term (Sch s1) (Sch s1) a
  QueryL : (q : RA s1 -> RA s3) -> a -> Term (Sch s1, Sch s2) (Sch s1, Sch s2) a
  QueryR : (q : RA s2 -> RA s3) -> a -> Term (Sch s1, Sch s2) (Sch s1, Sch s2) a
  Join   : {auto pS1 : NonEmpty s1} -> {auto pS2 : NonEmpty s2} -> Term (Sch s1, Sch s2) (Sch $ join s1 s2) a
  Done   : Term s1 s2 a

-- We can write program, but the type of the program vary with the
-- program! In this case, there is no chance to implement an
-- evaluation function! Next, see Fix point of a functor.

prg1 : Term (Sch phant.sql.scAgenda) (Sch phant.sql.scAgenda) a
prg1 = Done

prg2 : Term (Sch phant.sql.scAgenda) (Sch [Id, ("Addr", NAT)],
                                      Sch [Id, ("Date", TEXT 10), ("Name", TEXT 255)]) (
         Term (Sch [Id, ("Addr", NAT)],
               Sch [Id, ("Date", TEXT 10), ("Name", TEXT 255)])
              (Sch [Id, ("Addr", NAT)],
               Sch [Id, ("Date", TEXT 10), ("Name", TEXT 255)]) a)
prg2 = Frag [("Addr", NAT)]
       Done

prg3 : Term (Sch phant.sql.scAgenda) (Sch [Id, ("Addr", NAT)],
                                      Sch [Id, ("Date", TEXT 10), ("Name", TEXT 255)]) (
         Term (Sch [Id, ("Addr", NAT)],
               Sch [Id, ("Date", TEXT 10), ("Name", TEXT 255)])
              (Sch [Id, ("Addr", NAT)],
               Sch [Id, ("Date", TEXT 10), ("Name", TEXT 255)]) (
           Term (Sch [Id, ("Addr", NAT)],
                 Sch [Id, ("Date", TEXT 10), ("Name", TEXT 255)])
                (Sch [Id, ("Addr", NAT)],
                 Sch [Id, ("Date", TEXT 10), ("Name", TEXT 255)]) a))
prg3 = Frag [("Addr", NAT)] $
       QueryL (Project [("Date", TEXT 10)])
       Done

data Fix : (f : Type -> Type) -> Type where
  MkFix : f (Fix f) -> Fix f

prgFix1 : Fix (Term st1 st2)
prgFix1 = MkFix Done

prgFix2 : Fix (Term (Sch phant.sql.scAgenda)
                    (Sch [Id, ("Addr", NAT)], Sch [Id, ("Date", TEXT 10), ("Name", TEXT 255)]))
prgFix2 = MkFix (Frag [("Addr", NAT)] (MkFix Done))

-- prgFix3 : Fix (Term (Sch phant.sql.scAgenda) (Sch [("Addr", NAT)],
--                                               Sch [("Date", TEXT 10), ("Name", TEXT 255)]))
-- prgFix3 = MkFix (Frag [("Addr", NAT)] (MkFix (QueryL (Project [("Date", TEXT 10)]) (MkFix Done))))

data Fix' : (f : Type -> Type -> Type -> Type) -> (i : Type) -> (k : Type) -> Type where
  MkFix' : f i j (Fix' f j k) -> Fix' f i k

prgFix1' : Fix' Term s1 s2
prgFix1' = MkFix' Done {j=Type}

prgFix2' : Fix' Term (Sch phant.sql.scAgenda)
                     (Sch [Id, ("Addr", NAT)], Sch [Id, ("Date", TEXT 10), ("Name", TEXT 255)])
prgFix2' = MkFix' (Frag [("Addr", NAT)] (MkFix' Done {j=Type}))

prgFix3' : Fix' Term (Sch phant.sql.scAgenda)
                     (Sch [Id, ("Addr", NAT)], Sch [Id, ("Date", TEXT 10), ("Name", TEXT 255)])
prgFix3' = MkFix' (Frag [Id, ("Addr", NAT)] (MkFix' (QueryL (Project [("Date", TEXT 10)]) (MkFix' Done {j=Type}))))

prgFix4' : Fix' Term (Sch phant.sql.scAgenda)
                     (Sch phant.sql.scAgenda)
prgFix4' = MkFix' (Frag [("Addr", NAT)] (MkFix' Join))

prgFix5' : Fix' Term (Sch phant.sql.scAgenda)
                     (Sch phant.sql.scAgenda)
prgFix5' = MkFix' (Frag [("Addr", NAT)] (MkFix' (QueryL (Project [("Date", TEXT 10)]) (MkFix' Join))))

-- -- Free Monads
-- frag : (s1 : Schema) -> Free (Term (Sch s2) (Sch (intersect s1 s2), Sch (s2 \\ s1))) ()
-- frag s1 = Bind (Frag s1 $ Pure ())

-- query : (q : RA s1 -> RA s3) -> Free (Term (Sch s1) (Sch s1)) (RA s1 -> RA s3)
-- query q = Bind (Query q $ Pure q)

-- queryL : (q : RA s1 -> RA s3) -> Free (Term (Sch s1, Sch s2) (Sch s1 , Sch s2)) (RA s1 ->  RA s3)
-- queryL q = Bind (QueryL q $ Pure q)

-- queryR : (q : RA s2 -> RA s3) -> Free (Term (Sch s1, Sch s2) (Sch s1 , Sch s2)) (RA s2 -> RA s3)
-- queryR q = Bind (QueryR q $ Pure q)

-- done : Free (Term st1 st2) r
-- done = Bind Done

-- -- prg1' : Free (Term a b) r
-- -- prg1' = done

-- -- prg2' : Free (Term (Sch phant.sql.scAgenda) (Sch [("Addr", NAT)],
-- --                                              Sch [("Date", TEXT 10), ("Name", TEXT 255)])) r
-- -- prg2' = do

-- --   prg1'

-- -- prg3' : Free (Term (Sch phant.sql.scAgenda) (Sch [("Addr", NAT)],
-- --                                              Sch [("Date", TEXT 10), ("Name", TEXT 255)])) ()
-- -- prg3' = frag [("Addr", NAT)] >>= (\a => ?val)
-- --         -- queryL (Project [("Date", TEXT 10)])
