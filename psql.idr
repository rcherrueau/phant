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
module phant.sql

import Data.List

%default total

infixr 7 |:

namespace inclusion
  -- List Inclusion.
  --
  -- Assert that elements of the first list are elements of the second
  -- list.
  Include : List a -> List a -> Type
  Include xs ys = (z : _) -> Elem z xs -> Elem z ys

  -- Be an element of a singletong list implies to being the singleton
  elemSingleton : Elem z [x] -> z = x
  elemSingleton Here           = Refl
  elemSingleton (There zInNil) = absurd zInNil

  -- The first element of the first list is not an element of the
  -- second list implies that the inclusion doesn't holds.
  notFirstIn : (Elem x ys -> Void) -> Include (x :: xs) ys -> Void
  notFirstIn nxInYs xxsIncYs {x} {xs} = let xInYs  = xxsIncYs x Here in
                                        nxInYs xInYs

  -- The tail of the first list is not included implies the first list
  -- is not included.
  notTailInc : (Include xs ys -> Void) -> Include (x :: xs) ys -> Void
  notTailInc nxsIncYs xxsIncYs {x} {xs} =
                                 nxsIncYs (\z,zInXs => xxsIncYs z (There zInXs))

  -- The head of the first list is an element of the second list AND
  -- the tail of the first list is included in the second list implies
  -- that the first list is included in the second list.
  firstInRestInc : DecEq a => {x : a} -> Elem x ys -> Include xs ys ->
    Include (x :: xs) ys
  firstInRestInc xInYs xsIncYs {x} {xs} =
                                 \z,zInXxs => case decEq z x of
                                   Yes zIsX => rewrite zIsX in xInYs
                                   -- z ≠ x ∧ z ∈ (x :: xs) ⇒ z ∈ xs
                                   No nzIsX => let zInXs = getZInXs nzIsX zInXxs in
                                               xsIncYs z zInXs
    where
    getZInXs : (z = x -> Void) -> Elem z (x :: xs) -> Elem z xs
    getZInXs nzIsX zInXxs with (xs)
      -- zInLX : Elem z [x]
      getZInXs nzIsX zInLX  | [] = let zIsX = elemSingleton zInLX in
                                   void (nzIsX zIsX)
      -- If xs in not empty, then two possibilities:
      -- z is the first element of xs, so zInXxs is Here, so z and x
      -- are equal which is not possible according to our assumption
      getZInXs nzIsX Here          | (z :: tl) = void (nzIsX Refl)
        -- z is an element of xs, so we have to pop the proof to
        -- discard the `x`.
      getZInXs nzIsX (There zInTl) | (_ :: tl) = zInTl

  -- Is the elements of the first list are elements of the second
  -- list.
  isInclude : DecEq a => (xs : List a) -> (ys : List a) -> Dec (Include xs ys)
  isInclude []        ys         = Yes (\z,zinxs => case isElem z ys of
                                                      No contra => absurd zinxs
                                                      Yes prf   => prf)
  -- 2 Strategies:
  -- 1. First head is elem of ys. Then manage tail included in ys
  isInclude (x :: xs) ys with (isElem x ys)
    isInclude (x :: xs) ys | (No nxInYs)
                                 = No $ notFirstIn nxInYs
    isInclude (x :: xs) ys | (Yes xInYs) with (isInclude xs ys)
      isInclude (x :: xs) ys | (Yes xInYs) | (No nxsIncYs)
                                 = No (\xxsIncYs => notTailInc nxsIncYs xxsIncYs)
      isInclude (x :: xs) ys | (Yes xInYs) | (Yes xsIncYs)
                                 = Yes $ firstInRestInc xInYs xsIncYs
  -- 2. First tl included in xs. Then manage head is elem of ys
  -- isInclude (x :: xs) ys with (isInclude xs ys)
  --   isInclude (x :: xs) ys | (No nxsIncYs)
  --                                = No (\xxsIncYs => notTailInc nxsIncYs xxsIncYs)
  --   isInclude (x :: xs) ys | (Yes xsIncYs) with (isElem x ys)
  --     isInclude (x :: xs) ys | (Yes xsIncYs) | (Yes xInYs)
  --                                = Yes $ firstInRestInc xInYs xsIncYs
  --     isInclude (x :: xs) ys | (Yes xsIncYs) | (No nxInYs)
  --                                = No (\xxsIncYs => notFirstIn nxInYs xxsIncYs)

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
  -- String here to define type clases only on correct encryption scheme
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
namespace dbuniverse
  data U : Type where
    NAT   : U
    TEXT  : Nat -> U
    REAL  : U
    BOOL  : U
    CRYPT : U
    HOME  : U -> U

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
    x == y               = False

  instance DecEq U where
    decEq NAT       NAT       = Yes Refl
    decEq (TEXT x)  (TEXT y)  with (decEq x y)
      decEq (TEXT x)  (TEXT x)  | (Yes Refl)
                                = Yes Refl
      decEq (TEXT x)  (TEXT y)  | (No contra)
                                = No (\txIsTy => contra $ cong txIsTy {f=getNat})
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
                              = No (\hxIsHy => contra $ cong hxIsHy {f=getU})
        where
        getU : U -> U
        getU (HOME x) = x
        getU x        = x
    -- decEq (CRYPT x) (CRYPT y) = ?jkl
    decEq x         y         = No believemeNotEq
        where
        postulate believemeNotEq : x = y -> Void


-- I. Schemas, Tables and Rows
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
  (|:) : {n: String} -> el u -> Row xs -> Row $ (n, u) :: xs

-- A table is a list of `Row s`
Table : Schema -> Type
Table s = List (Row s)

-- Examples
scAgenda : Schema
scAgenda = [("Date", TEXT 10), ("Name", TEXT 255), ("Addr", NAT)]

row1 : Row scAgenda
row1 = "2015-07-08" |: "Alice" |: 0 |: RNil

row2 : Row scAgenda
row2 = "2015-07-08" |: "Bob"   |: 0 |: RNil

row3 : Row scAgenda
row3 = "2015-07-10" |: "Alice" |: 1 |: RNil

agenda : Table scAgenda
agenda = [row1, row2, row3]

-- II. Constructing queries

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
    Select  : RA s -> RA s
    -- Introduce
    Unit    : Table s -> RA s

-- Number of meeting per day
nbMeeting : RA s -> RA (intersect [("Date", TEXT 10)] s)
nbMeeting ra =
  -- Count $ Group [("Date", TEXT 10)] $ Project [("Date", TEXT 10)] ra
  Project [("Date", TEXT 10)] ra

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



-- Comment vérifier qu'un calcul ne fuite pas de données
PC : Type
PC = List (List Attribute)

data Leak : PC -> Schema -> Type where
  Here  : {auto p: Include pc s} -> Leak (pc :: pcs) s
  There : Leak pcs s -> Leak (pc :: pcs) s

-- Test inequality
-- https://groups.google.com/forum/#!msg/idris-lang/WvpU_-6glYM/h0r-tHDY_EUJ
data NotLeak : PC -> Schema -> Type where
  NLStop : NotLeak [] s
  NLPop  : NotLeak pcs s -> {p : Include pc s -> Void} -> {default Refl ok : No p = isInclude pc s}-> NotLeak (pc :: pcs) s


run : RA s -> {auto p: NotLeak [[("Da", TEXT 10)]] s} -> Unit
run ra = ()
