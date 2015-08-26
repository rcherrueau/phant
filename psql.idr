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

-- Cryptographic encryption
-- String here to define type clases only on correct encryption scheme
data Crypt : String -> a -> Type where
  Heq : a -> (pkey : String) -> Crypt "Heq" a
  AES : a -> (key : String) -> Crypt "AES" a

instance Eq a => Eq (Crypt "Heq" a) where
  (Heq a _) == (Heq b _)      = a == b

instance Eq a => Eq (Crypt "AES" a) where
  (AES a _) == (AES b _) = a == b

-- I. Schemas, Tables and Rows
-- Universe for Database allowed types (both `U` and `el`)
--
-- Every data constructor of U corresponds to a type.
data U : Type where
  NAT   : U
  TEXT  : Nat -> U
  REAL  : U
  BOOL  : U
  CRYPT : Crypt _ U -> U
  HOME  : U -> U

instance Eq U where
  NAT == NAT           = True
  (TEXT x) == (TEXT y) = x == y
  REAL == REAL         = True
  BOOL == BOOL         = True
  x == y               = False

-- Decoding function
el : U -> Type
el NAT       = Nat
el (TEXT k)  = String
el REAL      = Double
el BOOL      = Bool
el (CRYPT f) with (f)
  el (CRYPT f) | (Heq x pkey) = Crypt "Heq" x
  el (CRYPT f) | (AES x skey) = Crypt "AES" x
el (HOME k)  = el k

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

data Sub : List a -> List a -> Type where
  Stop : Sub [] l
  Pop  : Sub xs ys -> {auto p: Elem x ys} -> Sub (x :: xs) ys

data Leak : PC -> Schema -> Type where
  Here  : {auto p: Sub pc s} -> Leak (pc :: pcs) s
  There : Leak pcs s -> Leak (pc :: pcs) s

data Nop : a -> Bool -> Type where
  nopp : a -> Nop a False

run : RA s -> {auto p: Leak [[("Date", TEXT 10)]] s} -> Unit
run ra = ()

-- Test inequality
-- https://groups.google.com/forum/#!msg/idris-lang/WvpU_-6glYM/h0r-tHDY_EUJ
