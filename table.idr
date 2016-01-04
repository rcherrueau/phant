||| Table for Relational Algebra
|||
||| A table consists of a list of rows. A row is a sequence of values,
||| in accordance with the types dictated by the table's schema.
module phant.table

import schema
import utils

import Data.List

%default total

namespace row
  ||| A row for a table.
  |||
  ||| RNil corresponds to the row with an empty schema. To create a
  ||| row in a schema of the form `[(name, u), xs]`, you need to
  ||| provide an element of type `el u`, together with a row adhering
  ||| to the schema `s` (passing an element of `el u` as argument
  ||| allows to use Idris base type instead of `U` types)
  data Row : Schema -> Type where
       RNil : Row []
       (::) : {n : String} -> {u : U} -> el u -> Row xs -> Row $ (n, u) :: xs

  ||| Returns the value for an attribute.
  |||
  ||| Returns the value for an attribute based on the proof that the
  ||| attribute is an element of the Schema.
  attrV : (r : Row s) -> (p : Elem a s) -> el (snd a)
  attrV RNil      Here      impossible
  attrV RNil      (There _) impossible
  attrV (v :: as) Here      = v
  attrV (v :: as) (There x) = attrV as x

  includedRow : Row s' -> Include s s' -> Row s
  includedRow r sIncS' {s = []       }     = RNil
  includedRow r sIncS' {s = ((n,u) :: xs)} =
                         let v = attrV r (sIncS' (n,u) Here)
                             r = (includedRow r (includeReduc sIncS'))
                         in v :: r

--   -- Better row (with pair)
--   -- I should go with a definition of schema that make imposible the
--   -- empty list to avoid the NonEmpty proof. The implementation may
--   -- look like that
--   Row : (s : Schema) -> {auto ok : NonEmpty s} -> Type
--   Row []                     {ok} = absurd ok
--   Row [(_,u)]                {ok} = el u
--   Row ((_,u) :: s@(a :: as)) {ok} = Pair (el u) (Row s)

--   schema : {auto ok : NonEmpty s} -> Row s {ok}  -> Schema
--   schema _ {s} = s


-- Table : (s : Schema) -> {auto ok : NonEmpty s} -> Type
-- Table s = List (Row s)

-- TODO getName, getVal, hasColumn ...

-- A table is a list of `Row s`
Table : Schema -> Type
Table s = List (Row s)
