module phant.laws

import schema
import table
import utils
import ra

import Data.List

%default total

and : {s : Schema} -> (ql : Row sl -> Bool) -> (qr : Row sr -> Bool) ->
      {auto inc : Include sl s} -> {auto inc' : Include sr s} ->
      Row s -> Bool
and ql qr r {inc} {inc'} = let rsl = includedRow r inc
                               rsr = includedRow r inc'
                           in (ql rsl) && (qr rsr)

-- To implement s1, s2, I need a term for predicate on a row (rather
-- than using pure idris). The advantages of using pure idris is that
-- the type checker does the job for us.
using (a: Schema, ā: Schema, aā: defrag (a,ā),
       -- a/ā got an Id
       idINa : Elem Id a, idINā : Elem Id ā,
       -- a/ā is included in aā
       aINCaā : Include a (defrag (a,ā)), āINCaā : Include ā (defrag (a,ā)),
       -- inclusion is not strict
       aINCa : Include a a,
       āINCā : Include ā ā,
       aāINCaā : Include (defrag (a,ā)) (defrag (a,ā)))
  -- ∀ (a,ā), σ_{a} ∘ defrag_{a} ≡ defrag_{a} ∘ (σ_{a}, id)
  s3 : (pa : Row a -> Bool) ->
       -- Equality
       (Select pa {inc=aINCaā}) . (Defrag {idInS=idINa} {idInS'=idINā}) =
       (Defrag {idInS=idINa} {idInS'=idINā}) . (map2 (Select pa {inc=aINCa}) id)

    -- ∀ (a,ā), σ_{ā} ∘ defrag_{a} ≡ defrag_{a} ∘ (id, σ_{ā})
  s4 : (pā : Row ā -> Bool) ->
       -- Equality
       (Select pā {inc=āINCaā}) . (Defrag {idInS=idINa} {idInS'=idINā}) =
       (Defrag {idInS=idINa} {idInS'=idINā}) . (map2 id (Select pā {inc=āINCā}))

  -- ∀ (a,ā), σ_{a∧ā} ∘ defrag_{a} ≡ defrag_{a} ∘ (σ_{a}, σ_{ā})
  s5 : (pa : Row a -> Bool) -> (pā : Row ā -> Bool) ->
       -- Equality
       (Select (and pa pā {inc= aINCaā} {inc'=āINCaā}) {inc=aāINCaā})
       . (Defrag {idInS=idINa} {idInS'=idINā}) =
       (Defrag {idInS=idINa} {idInS'=idINā})
       . (map2 (Select pa {inc=aINCa}) (Select pā {inc=āINCā}))
