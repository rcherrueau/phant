-- The power of Pi, Relational Algebra
--
-- @InProceedings{OS08a,
--   author =       {Nicolas Oury and Wouter Swierstra},
--   title =        {The power of Pi},
--   booktitle =    {Proceeding of the 13th {ACM} {SIGPLAN} international
--                   conference on Functional programming, {ICFP} 2008,
--                   Victoria, BC, Canada, September 20-28, 2008},
--   pages =        {39--50},
--   year =         2008,
--   url =          {http://doi.acm.org/10.1145/1411204.1411213},
--   doi =          {10.1145/1411204.1411213}
-- }


-- TODO: https://groups.google.com/forum/#!topic/idris-lang/vuLe6gPmnlI
-- TODO: https://gist.github.com/cbiffle/82d15e015ab1191b73c3

module phant.sql

import Data.List
-- import Data.VectType

%default total

infixr 7 |:

-- List intersection.
namespace intersect
  -- Intersection operation
  %hide List.intersect
  intersect : Eq a => List a -> List a -> List a
  intersect [] ys = []
  intersect (x :: xs) ys with (elem x ys)
    intersect (x :: xs) ys | True  = x :: (intersect xs ys)
    intersect (x :: xs) ys | False = intersect xs ys

  -- Some lemmas specifying the semantic of intersection
  lemma_intersectNil : Eq a => (s : List a) -> intersect s [] = []
  lemma_intersectNil []        = Refl
  lemma_intersectNil (x :: xs) = lemma_intersectNil xs

  postulate lemma_intersectReducX : Eq a => (xs, ys : List a) -> (z : a) ->
                                    (z = x -> Void) ->
                                    Elem z (intersect (x :: xs) ys) ->
                                    intersect (x :: xs) ys = intersect xs ys

  postulate lemma_intersectReducY : Eq a => (xs, ys : List a) -> (z : a) ->
                                    (z = y -> Void) ->
                                    Elem z (intersect xs (y :: ys)) ->
                                    intersect xs (y :: ys) = intersect xs ys

  -- In intersection predicate
  InIntersection : a -> List a -> List a -> Type
  InIntersection z xs ys = (Elem z xs, Elem z ys)

  -- Decides whether an element is in the intersection of two list or not
  inIntersection : DecEq a => (z : a) -> (xs : List a) -> (ys : List a) ->
                   Dec (InIntersection z xs ys)
  inIntersection z xs ys with (isElem z xs)
    inIntersection z xs ys | (Yes zinxs) with (isElem z ys)
      inIntersection z xs ys | (Yes zinxs) | (Yes zinys) =
                                           Yes (zinxs, zinys)
      inIntersection z xs ys | (Yes zinxs) | (No zninys) =
                                           No (\(_,zinys) => zninys zinys)
    inIntersection z xs ys | (No zninxs) = No (\(zinxs,_) => zninxs zinxs)

  -- z ∈ (xs ∩ ys) ⇒ z ∈ xs ∧ z ∈ ys
  elemInter : (Eq a, DecEq a) => (xs, ys : List a) -> (z : a) ->
              Elem z (intersect xs ys) -> InIntersection z xs ys
  elemInter xs ys z zInZs = let zInXs = elemInterXs xs ys z zInZs in
                            let zInYs = elemInterYs xs ys z zInZs in
                            (zInXs, zInYs)
    where
    elemInterXs : (Eq a, DecEq a) => (xs, ys : List a) -> (z : a) ->
                  Elem z (intersect xs ys) -> Elem z xs
    elemInterXs []        _  z zInZs = zInZs
    elemInterXs (x :: xs) ys z zInZs with (decEq z x)
      elemInterXs (z :: xs) _  z zInZs  | (Yes Refl)  = Here
      elemInterXs (x :: xs) ys z zInZs  | (No contra) =
                                let zInZsReduc = ?zInZsReducX in
                                let zInXs = elemInterXs xs ys z zInZsReduc in
                                There zInXs

    elemInterYs : (Eq a, DecEq a) => (xs, ys : List a) -> (z : a) ->
                  Elem z (intersect xs ys) -> Elem z ys
    elemInterYs xs []        z zInZs =
                                rewrite sym $ lemma_intersectNil xs in zInZs
    elemInterYs xs (y :: ys) z zInZs with (decEq z y)
      elemInterYs xs (z :: ys) z zInZs | (Yes Refl) = Here
      elemInterYs xs (y :: ys) z zInZs | (No contra) =
                                let zInZsReduc = ?zInZsReducY in
                                let zInYs = elemInterYs xs ys z zInZsReduc in
                                There zInYs

-- List Inclusion.
namespace inclusion
  -- Inclusion predicate
  --
  -- Asserts that the elements of the first list are elements of the
  -- second list.
  -- Axiom of power set:
  -- https://en.wikipedia.org/wiki/Axiom_of_power_set
  Include : List a -> List a -> Type
  Include xs ys = (z : _) -> Elem z xs -> Elem z ys

  -- Reduction of the Include predicate
  includeReduc : Include (x :: xs) ys -> Include xs ys
  includeReduc xxsIncYs = \z,zInXs => xxsIncYs z (There zInXs)

  -- Being an element of a singleton list implies to be that singleton
  elemSingleton : Elem z [x] -> z = x
  elemSingleton Here           = Refl
  elemSingleton (There zInNil) = absurd zInNil

  -- Being an element of a non empty list and not being the fisrt
  -- element implies to be an element of the tail.
  elemTail : (z = hd -> Void) -> Elem z (hd :: tl) -> Elem z tl
  -- (z ∈ [hd] => z = hd) ∧ z ≠ hd
  elemTail nzIsHd zInHdTl   {tl = []} = let zIsHd = elemSingleton zInHdTl in
                                        void $ nzIsHd zIsHd
  -- (z ∈ z :: tl => z = hd) ∧ z ≠ hd
  elemTail nzIsHd Here      {tl}      = void $ nzIsHd Refl
  -- z ∈ _ :: tl => z ∈ tl
  elemTail nzIsHd (There p) {tl}      = p

  -- Is the elements of the first list are elements of the second
  -- list.
  isIncluded : DecEq a => (xs : List a) -> (ys : List a) ->
               Dec (Include xs ys)
  -- This definition seems correct since I cannot provide any `z` due
  -- to the empty `xs`.
  isIncluded []        ys         = Yes (\z,zInXs => absurd zInXs)
  -- First check if `xs` is included in `ys` or not.
  isIncluded (x :: xs) ys with (isIncluded xs ys)
    isIncluded (x :: xs) ys | (No nxsIncYs) =
                               No $ notTailInc nxsIncYs
      where
      notTailInc : (Include xs ys -> Void) -> Include (x :: xs) ys -> Void
      notTailInc nxsIncYs xxsIncYs = nxsIncYs (\z,zInXs =>
                                                 xxsIncYs z (There zInXs))

    isIncluded (x :: xs) ys | (Yes xsIncYs) with (isElem x ys)
      -- Then manage `x` is an element of `ys` or not.
      isIncluded (x :: xs) ys | (Yes xsIncYs) | (Yes xInYs) =
                               Yes $ headInTailInc xInYs xsIncYs
        where
        headInTailInc : Elem x ys -> Include xs ys -> Include (x :: xs) ys
        headInTailInc xInYs xsIncYs = \z,zInXxs => case decEq z x of
                         No nzIsX => let zInXs = elemTail nzIsX zInXxs in
                                     xsIncYs z zInXs
                         Yes zIsX => rewrite zIsX in xInYs

      isIncluded (x :: xs) ys | (Yes xsIncYs) | (No nxInYs) =
                               No $ notHeadIn nxInYs
        where
        notHeadIn : (Elem x ys -> Void) -> Include (x :: xs) ys -> Void
        notHeadIn nxInYs xxsIncYs = let xInYs = xxsIncYs x Here in
                                    nxInYs xInYs

  -- The result of the intersection between two list `xs` and `ys` is
  -- both included in `xs` and `ys`.
  intersectIncluded : (Eq a, DecEq a) => (xs, ys : List a) ->
                      (Include (intersect xs ys) xs,
                       Include (intersect xs ys) ys)
  intersectIncluded xs ys =
    let zsIncXs = \z,zInZs => fst $ elemInter xs ys z zInZs in
    let zsIncYs = \z,zInZs => snd $ elemInter xs ys z zInZs in
    (zsIncXs, zsIncYs)

-- Cryptographic encryption
namespace encryption
  Key : Type
  Key = String

  class Crypt a where
    encrypt : String -> Key -> a
    decrypt : a -> Key -> String

  -- AES
  data AES : Type where
    MkAES : String -> AES

  instance Crypt AES where
    encrypt s k = MkAES s
    decrypt a k = "str"

  instance Eq AES where
    (MkAES x) == (MkAES y) = x == y

  -- Cryptographic encryption
  -- String here defines type clases only on correct encryption scheme
  -- data Crypt : String -> a -> Type where
  --   Heq : a -> (pkey : String) -> Crypt "Heq" a
  --   AES : a -> (key : String) -> Crypt "AES" a

  -- instance Eq a => Eq (Crypt "Heq" a) where
  --   (Heq a _) == (Heq b _)      = a == b

  -- instance Eq a => Eq (Crypt "AES" a) where
  --   (AES a _) == (AES b _) = a == b

  -- -- in data U:
  -- CRYPT : Crypt _ U -> U

  -- -- in el
  -- el (CRYPT f) with (f)
  --   el (CRYPT f) | (Heq x pkey) = Crypt "Heq" x
  --   el (CRYPT f) | (AES x skey) = Crypt "AES" x


-- Universe for Database allowed types (both `U` and `el`)
--
-- Every data constructor of U corresponds to a type.
namespace rauniverse
  data U = NAT
         | TEXT Nat
         | REAL
         | BOOL
         | CRYPT
         | HOME U

  -- Decoding function
  el : U -> Type
  el NAT       = Nat
  el (TEXT k)  = String
  el REAL      = Double
  el BOOL      = Bool
  el CRYPT     = AES
  el (HOME k)  = el k

  instance Eq U where
    NAT == NAT           = True
    (TEXT x) == (TEXT y) = x == y
    REAL == REAL         = True
    BOOL == BOOL         = True
    (HOME x) == (HOME y) = x == y
    CRYPT == CRYPT       = True
    _ == _               = False

  instance DecEq U where
    decEq NAT       NAT       = Yes Refl
    decEq (TEXT x)  (TEXT y)  with (decEq x y)
      decEq (TEXT x)  (TEXT x)  | (Yes Refl)
                              = Yes Refl
      decEq (TEXT x)  (TEXT y)  | (No contra)
                              = No (\txIsTy =>
                                      contra $ cong txIsTy {f = getNat})
        where
        getNat : U -> Nat
        getNat (TEXT x) = x
        getNat _        = Z
    decEq REAL      REAL      = Yes Refl
    decEq BOOL      BOOL      = Yes Refl
    decEq (HOME x)  (HOME y)  with (decEq x y)
      decEq (HOME x)  (HOME x)  | (Yes Refl)
                              = Yes Refl
      decEq (HOME x)  (HOME y)  | (No contra)
                              = No (\hxIsHy =>
                                      contra $ cong hxIsHy {f = getU})
        where
        getU : U -> U
        getU (HOME x) = x
        getU x        = x
    -- decEq (CRYPT x) (CRYPT y) = ?jkl
    -- I should go like
    -- https://github.com/david-christiansen/IdrisSqlite/blob/master/type-provider-demo/SQLiteTypes.idr
    decEq x         y         = No believemeNotEq
        where
        postulate believemeNotEq : x = y -> Void


-- Relational Algebra
namespace ra
  -- A schema describes the type of a table.
  --
  -- It consists of a set of pairs of column names and types. We do not
  -- allow any type to occur in a Schema, but restrict ourself to the
  -- Univers (U, el)
  Attribute: Type
  Attribute = (String, U)

  Schema : Type
  Schema = List Attribute

  -- Now we have our schema, we can define a table. A table consists of
  -- a list of rows. A row is a sequence of values, in accordance with
  -- the types dictated by the table's schema.

  -- A row for a table.
  --
  -- RNil corresponds to the row with an empty schema. To create a row
  -- in a schema of the form `[(name, u), xs]`, you need to provide an
  -- element of type `el u`, together with a row adhering to the schema
  -- `s` (passing an element of `el u` as argument allows to use Idris
  -- base type instead of `U` types)
  data Row : Schema -> Type where
    RNil : Row Nil
    (|:) : {n : String} -> {u : U} -> el u -> Row xs -> Row $ (n, u) :: xs

  -- A table is a list of `Row s`
  Table : Schema -> Type
  Table s = List (Row s)

  -- A query expression (Relation Algebra)
  --
  -- An expression of `RA s` corresponds to a query that will return a
  -- table with schema `s`. Operations are those ones of relational
  -- algebra.
  --
  -- Relational algebra uses set union, set difference and cartesian
  -- product from set theory, but adds additional constraints. Unions
  -- and difference must be /union-compatible/, i.e., the two relations
  -- must have the *same set of attributes*.
  --
  -- Cartesion product must have disjoint headers.
  -- See, https://en.wikipedia.org/wiki/Relational_algebra#Set_operators
  using (s: Schema, s': Schema)
    data RA : Schema -> Type where
      -- Set operatos
      Union   : RA s -> RA s -> RA s
      Diff    : RA s -> RA s -> RA s
      Product : RA s -> RA s' -> RA (s ++ s')
      -- Others
      Project : (s : Schema) -> RA s' -> RA (intersect s s')
      Select  : (Row s -> Bool) -> RA s -> RA s
      Join   : RA s -> RA s' -> RA (nubBy (\a1,a2 => (fst a1) == (fst a2)) (s ++ s'))
      -- Introduce
      Unit    : (s : Schema) -> RA s

-- namespace raoperational
--   attrEq : {u,v : U} -> el u -> el v -> Bool
--   attrEq x y {u = NAT}      {v = NAT}      = x == y
--   attrEq x y {u = NAT}      {v}            = False
--   attrEq x y {u = (TEXT k)} {v = (TEXT L)} = x == y
--   attrEq x y {u = (TEXT k)} {v}            = False
--   attrEq x y {u = REAL}     {v = REAL}     = x == y
--   attrEq x y {u = REAL}     {v}            = False
--   attrEq x y {u = BOOL}     {v = BOOL}     = x == y
--   attrEq x y {u = BOOL}     {v}            = False
--   attrEq x y {u = CRYPT}    {v = CRYPT}    = x == y
--   attrEq x y {u = CRYPT}    {v}            = False
--   attrEq x y {u = (HOME h)} {v = (HOME i)} = attrEq {u=h} {v=i} x y
--   attrEq x y {u = (HOME z)} {v}            = False

--   instance Eq (Row s) where
--     RNil          == RNil            = True
--     (attr |: row) == (attr' |: row') = attrEq attr attr' && row == row'

--   union : Table s -> Table s -> Table s
--   union t1 t2 = List.union t1 t2

--   diff : Table s -> Table s -> Table s
--   diff t1 t2 = t1 \\ t2

--   product : Table s -> Table s' -> Table (s ++ s')
--   product t1 t2 = [ union r1 r2 | r1 <- t1, r2 <- t2 ]
--     where
--     union : Row s -> Row s' -> Row (s ++ s')
--     union RNil       r  = r
--     union (a |: r1)  r2 = a |: union r1 r2

--   project : (s : Schema) -> Table s' -> Table (intersect s s')
--   project s t {s'} = let zs = intersect s s' in
--                      let zsIncS' = snd $ intersectIncluded s s' in
--                      [ project r zsIncS' | r <- t ]
--     where
--     get : {s : Schema} -> (a : Attribute) -> Row s ->  Elem a s -> el (snd a)
--     get _ (v |: r) Here      = v
--     get a (v |: r) (There p) = get a r p

--     project : Row s' -> Include zs s' -> Row zs
--     project r inc {zs = []         } = RNil
--     project r inc {zs = (n,u) :: xs} =
--                     let hypo = project r (includeReduc inc) in
--                     let nuInS' = inc (n,u) Here in
--                     let val = get (n,u) r nuInS' in
--                     val |: hypo

--   select : (Row s -> Bool) -> Table s -> Table s
--   select p t = [ r | r <- t, p r ]

--   run : RA s -> Table s
--   run (Union q r)   = raoperational.union (run q) (run r)
--   run (Diff q r)    = diff (run q) (run r)
--   run (Product q r) = product (run q) (run r)
--   run (Project s q) = project s (run q)
--   run (Select p q)  = select p (run q)
--   run (Unit table)  = table

-- namespace leak
--   -- Privacy Constraints Specification
--   PC : Type
--   PC = List (List Attribute)

--   -- Leak predicate.
--   --
--   -- Ensures that an Privacy Constraint leaks
--   data Leak : PC -> Schema -> Type where
--     Here  : {auto p: Include pc s} -> Leak (pc :: pcs) s
--     There : Leak pcs s -> Leak (pc :: pcs) s

--   -- Zero leak predicate.
--   --
--   -- Ensures that no Privacy Constraints leak.
--   data ZeroLeak : PC -> Schema -> Type where
--     ZLStop : ZeroLeak [] s
--     -- In idris this is how test inequality
--     -- https://groups.google.com/forum/#!msg/idris-lang/WvpU_-6glYM/h0r-tHDY_EUJ
--     NLPop  : ZeroLeak pcs s -> {p : Include pc s -> Void} ->
--       {default Refl ok : No p = isIncluded pc s} -> ZeroLeak (pc :: pcs) s

--   -- test
--   runZL: RA s -> {auto p : ZeroLeak [[("Date", TEXT 10)]] s} -> Table s
--   runZL ra = raoperational.run ra
--   -- runZl (Unit agenda) -- Can't solve goal NotLeak [[("Date", TEXT 10)]]
--   -- runZl (Project [("Addr", NAT)] $ Unit agenda)

--   -- impossibru
--   -- run' : RA s -> PC -> Unit
--   -- run' ra pc {s} = let noleak = proofNoLeak in ()
--   --   where
--   --   proofNoLeak : (ZeroLeak pc s)
--   --   proofNoLeak = ?project

-- Examples
scAgenda : Schema
scAgenda = [("Date", TEXT 10), ("Name", TEXT 255), ("Addr", NAT)]

-- Qualify the name according to Idris 0.9.20 and its new rules for
-- lower-case names in type signatures.
-- https://github.com/idris-lang/Idris-dev/issues/2673
-- row1 : Row phant.sql.scAgenda
-- row1 = "2015-07-08" |: "Alice" |: 0 |: RNil

-- row2 : Row phant.sql.scAgenda
-- row2 = "2015-07-08" |: "Bob"   |: 0 |: RNil

-- row3 : Row phant.sql.scAgenda
-- row3 = "2015-07-10" |: "Alice" |: 1 |: RNil

-- agenda : Table phant.sql.scAgenda
-- agenda = [row1, row2, row3]


-- Number of meeting per day
nbMeeting : RA s -> RA (intersect [("Date", TEXT 10)] s)
nbMeeting ra =
  -- Count $ Group [("Date", TEXT 10)] $ Project [("Date", TEXT 10)] ra
  Project [("Date", TEXT 10)] ra

raAgenda : RA phant.sql.scAgenda
raAgenda = Unit scAgenda

testJoin : RA phant.sql.scAgenda
testJoin = Join raAgenda raAgenda

testJoin2 : RA [("Date", TEXT 10), ("Name", TEXT 255), ("Addr", NAT), ("Id", NAT)]
testJoin2 = Join (Project [("Date", TEXT 10), ("Id", NAT)] $ raAgenda)
                  (Product raAgenda (Unit [("Id", NAT)]))


-- test: Table [("Date", TEXT 10)]
-- test = project [("Date", TEXT 10)] agenda

-- test2 : Table [("Date", TEXT 10)]
-- test2 = run $ nbMeeting (Unit agenda)

-- test3 : Table [("Date", TEXT 10)]
-- test3 = run (Project [("Date", TEXT 10)] $
--              Select (\r => let (d,n,a) = row2Tuple r in
--                            d == "2015-07-08") $
--              Unit agenda)
--   where
--   row2Tuple : Row phant.sql.scAgenda -> (String, String, Nat)
--   row2Tuple (d |: n |: a |: RNil) = (d,n,a)

-- test4 : Table [("Date", TEXT 10)]
-- test4 = run (Project [("Date", TEXT 10)] $
--              Select (\(d |: _ |: _ |: RNil ) => d == "2015-07-08") $
--              Unit agenda)

-- Some thought:
-- Symbolic simulations
--
-- Symbolic simulations are like deterministic simulations one
-- concrete data, using symbolic values to run and check the results
-- of a /full set/ of simulations. See,
-- http://coq-blog.clarus.me/checking-concurrent-programs-with-symbolic-simulations.html
--
-- A simulation, or a run, is a co-program over an interactive query.
-- It answers to the requests of the program, playing th role of the
-- environment. A simulation is defined by induction over the
-- program's structure. This has two advantages:
-- - By construction, a simulation must give exactly one answer per
--   request.
-- - You can construct the simulation following the structure of the
--   program.

-- C'est quoi le point de variation dans mon programe ?
-- 1. Le schema de la base
-- 2. Les requêtes fait sur un schéma
-- 3. Le calcul utilisés pour protéger le schéma

-- Du coup, qu'est ce que je peux tester pour la propriété de fuite
-- des données ?
-- 1. Pour n'importe quel schéma, mon calcule ne fuite pas d'info :
--    Impossible a vérifier car les protection dépendent du schéma.
-- 2. Pour n'importe quelle requête (sur un schéma), mon calcule ne
--    fuite pas d'info : OK.
-- 3. Utiliser le prover pour driver l'écriture d'un calcul safe pour
--    n'importe quelle requête lorsque je connais le schéma.
-- On se focalise sur 2 et 3.

-- Qu'est-ce que le calcul ? Le calcule est une combinaison d'une
-- requête et de fonctions de protections entrelacées. Typiquement, je
-- peux représenter mon calcule par une monade.

---------- Proofs ----------

phant.sql.intersect.zInZsReducX = proof
  intros
  rewrite lemma_intersectReducX xs ys z contra zInZs
  exact zInZs


phant.sql.intersect.zInZsReducY = proof
  intros
  rewrite lemma_intersectReducY xs ys z contra zInZs
  exact zInZs
