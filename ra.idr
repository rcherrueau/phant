module phant.ra

import public schema
import utils
import crypt

import Data.List
import Data.Vect

%default total
%access public

Ctx : Type
Ctx = U

using (n : Nat, a : U, b : U, u : U,
  bctx : Vect n Ctx, bctx' : Vect m Ctx, bctx'' : Vect l Ctx,
  p : Process, p' : Process, p'' : Process,
  s : Schema, s' : Schema, s'': Schema)

