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

  data HasType : Vect n Ctx -> Fin n -> Ctx -> Type where
    Stop : HasType (ctx :: bctx) FZ ctx
    Pop  : HasType bctx i ctx -> HasType (x :: bctx) (FS i) ctx

  data Query : U -> Vect n Ctx -> Type where
    QVal     : (el u) -> Query u bctx
    QVar     : HasType bctx i u -> Query u bctx
    -- OP/2
    QEq      : Eq (el u) =>
               Query u bctx -> Query u bctx' -> Query BOOL bctx'
    QElem    : Eq (el u) =>
               Query u bctx -> Query (SCH s) bctx' -> Query BOOL bctx'
    -- SQL/1
    QProject : (sproj : Schema) ->
               Query (SCH s) bctx -> Query (SCH (intersect sproj s)) bctx
    QSelect  : (a : Attribute) ->
               (p : Query (getU a) bctx -> Query BOOL bctx) ->
               {auto elem : Elem a s} ->
               Query (SCH s) bctx -> Query (SCH s) bctx
    QCount   : (scount : Schema) ->
               {default (includeSingleton Here) inc : Include scount s} ->
               Query (SCH s) bctx -> Query (SCH (count scount s {inc})) bctx
    -- SQL/2
    QProduct : Query (SCH s) bctx -> Query (SCH s') bctx' ->
               Query (SCH (s * s')) bctx'
