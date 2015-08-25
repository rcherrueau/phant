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


-- I. Schemas, Tables and Rows

-- Universe for Database allowed types (both `U` and `el`)
--
-- Every data constructor of U corresponds to a type.
data U : Type where
  NAT  : U
  TEXT : Nat -> U
  REAL : U
  BOOL : U

instance Eq U where
  NAT == NAT       = True
  (TEXT x) == (TEXT y) = x == y
  REAL == REAL     = True
  BOOL == BOOL     = True
  x == y           = False

-- Decoding function
el : U -> Type
el NAT      = Nat
el (TEXT k) = String
el REAL     = Double
el BOOL     = Bool

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
    Read    : Table s -> RA s

-- Number of meeting per day
SELECT $ Project [("Date", TEXT 10)] $ Read agenda
