||| Table for Relational Algebra
|||
||| A table consists of a list of rows. A row is a sequence of values,
||| in accordance with the types dictated by the table's schema.
module phant.table

import schema

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

  schema : Row s -> Schema
  schema _ {s} = s

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
