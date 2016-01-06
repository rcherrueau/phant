module phant.pv

import guard
import Effects

%access public

||| Powerset of a list
-- http://evan-tech.livejournal.com/220036.html
powerset : List a -> List (List a)
powerset = filterM (const [True, False])
  where
  filterM : Monad m => (a -> m Bool) -> List a -> m (List a)
  filterM _ []        = return []
  filterM p (x :: xs) = do flg <- p x
                           ys <- filterM p xs
                           return (if flg then x :: ys else ys)

||| Type for a Privay Constraint.
|||
||| ````idris example
||| the PC [("Date", NAT), ("Addr", NAT)]
||| ````
PC : Type
PC = List Attribute

||| Returns the list of privacy constraints that match on a specific
||| schema.
getInnerPCs : Schema -> List PC -> List PC
getInnerPCs s = filter (flip included s)
  where
  ||| Tests if the first list is included in the second.
  included : Eq a => List a -> List a -> Bool
  included xs ys = all (flip elem ys) xs

||| Makes an identifier from an attribute.
mkAttrId : Attribute -> String
mkAttrId = name

||| Makes an identifier from a list of attribute.
mkAttrsId : List Attribute -> String
mkAttrsId = concat . map mkAttrId

||| Makes variable identifier form an attribute.
mkAttrVId : Attribute -> String
mkAttrVId = (++) "a" . mkAttrId

||| Makes a raw identifier from an attribute.
mkRawAttId : Attribute -> String
mkRawAttId a = "raw(" ++ (mkAttrId a) ++ ")"

||| Generates a forall term.
|||
||| <forall> := forall <attrVId>: attribute, ...;
|||
||| This generates the forall term for a list of attributes. The
||| generation uses the original schema and produce a varialble for
||| each missing attribute. If the original schema and the list of
||| attributes are equivalent, then no forall term is produced.
|||
||| @ s  The original schema.
||| @ as The list of attributes targeting the forall.
genForAll : (s : Schema) -> (as : List Attribute) -> IO ()
genForAll s as with (s \\ as)
  genForAll s as | []  = putStr "" -- no forall
  genForAll s as | out = do        -- forall
    let attrVIds = map (flip (++) ": attribute" . mkAttrVId) out
    putStr "forall "
    putStr $ concat (intersperse ", " attrVIds)
    putStr ";"


||| Generate an underlying schema.
|||
||| Generate an underlying schema based on the original one. If an
||| attribute of `s` is in `us` then it produces a readable attribute
||| (raw). Otherwise it produces a variable attribute.
|||
||| <uschema> := (<attr>, ...)
||| <attr>    := <rawAttrId> | <attrVId>
|||
||| @ s  the original schema
||| @ us the underlying schema
genUSchema : (s : Schema) -> (us : List Attribute) -> IO ()
genUSchema s us = do
  let attrs = map (\a => case (elem a us) of
                           True  => mkRawAttId a
                           False => mkAttrVId a) s
  putStr $ "(" ++ (concat (intersperse ", " attrs)) ++ ")"

-- Can I get the list of attribute, the state of the cloud and the
-- list of pc, from a Guard effect ? Yes for the list of attribute and
-- the cloud state :
--
-- > testPV : Eff r [GUARD $ Plain $ s@@ip] [GUARD $ FragV (sl@@ipl) (sr@@ipr)] -> (Schema, CState, List Schema)
-- > testPV x {s} {sl} {ipl} {sr} {ipr} = (s, FragV (sl @@ ipl) (sr @@ ipr), [])
--
-- If I take the list of attribute in arguments, then I can generate
-- all the first part of the file. Let's do this, but first define
-- what is a list of pc:
--
--
-- The prelude of a pv file should look like something like this
prelude : Schema -> List PC -> IO ()
prelude s pcs = do
    genDefault
    putStrLn "(* ----------------------------------------------- DB attribute and PC *)"
    putStrLn "(* Database attributes *)"
    genDbAttrs s
    putStrLn "(* Privacy constraints -- Attacker *)"
    genAttacker pcs
    putStrLn "(* Instruction for an attacker: what is a PC *)"
    genDeducsPC s pcs
    putStrLn "(* ----------------------------------------------------- DB Operations *)"
    putStrLn "(* Projections *)"
    putStrLn "(* Selections *)"
    putStrLn "(* Grouping *)"
    putStrLn "(* Aggregation *)"
    putStrLn "(* -------------------------------------------------------------- Main *)"

  where
  genDefault : IO ()
  genDefault = putStrLn $
    unlines [
      "set ignoreTypes = false.",
      "(* set traceDisplay = long. *)",
      "",
      "(* Debug: test if reduction rules applied correctly *)",
      "event NO_RULE.",
      "query event(NO_RULE).",
      "",
      "(* Attribute of the database *)",
      "type attribute.",
      "const unit: attribute.  (* unit: attribute without information *)",
      "fun raw(bitstring): attribute [data]. (* raw: constructor for attribute  *)",
      "(* A raw is labelised by its position in the schema *)",
      "",
      "(* ------------------------------------------------ Privacy Operations *)",
      "(* Defragmentation *)",
      "reduc forall vd: attribute, vn: attribute, va: attribute;",
      "defrag((vd,unit,unit), (unit,vn,va)) = (vd,vn,va).",
      "",
      "(* Symmetric Encryption *)",
      "type skey.",
      "fun senc(bitstring, skey): attribute.",
      "reduc forall m: bitstring, sk: skey; sdec(senc(m, sk), sk) = raw(m).",
      "",
      "(* Homomorphic Encryption *)",
      "type pkey.",
      "fun pk(skey): pkey.",
      "fun henc(bitstring, pkey): attribute.",
      "reduc forall m: bitstring, sk: skey; hdec(henc(m, pk(sk)), sk) = raw(m).",
      ""]

  ||| Generate the database attributes.
  ||| <dbAttr> := const <attrId>: bitstring [private]. ...
  genDbAttrs : List Attribute -> IO ()
  genDbAttrs as = do
    let dbAttrs = map (\a => "const "
                             ++ (mkAttrId a)
                             ++ ": bitstring [private].") as
    sequence (map putStrLn dbAttrs)
    putStrLn ""

  ||| Generate the attacker model.
  ||| <attack> := <const> ...
  |||             <query> ...
  ||| <const>  := const pc_<attrsId>: bistring [private].
  ||| <query>  := query attacker(pc_<attrsId>).
  genAttacker : List PC -> IO ()
  genAttacker pcs = do
    let pcAttrsIds = map  ((++) "pc_" . mkAttrsId) pcs
    let consts = map (\id => "const " ++ id ++ ": bitstring [private].")
                     pcAttrsIds
    let querys = map (\id => "query attackers(" ++ id ++ ").")
                     pcAttrsIds
    sequence (map putStrLn consts)
    putStrLn ""
    sequence (map putStrLn querys)
    putStrLn ""


  ||| Generates the deduction rules that produces PCs
  |||
  ||| <deducPC> := reduc <forall>
  |||              confidential_<attrsId>(<uschema>) = <inpcs>.
  ||| <inpcs>   := (pc_<attrsId>, ...)
  genDeducPC : Schema -> List Attribute -> List PC -> IO ()
  genDeducPC s as []  = putStr ""
  genDeducPC s as pcs = do
    let attrsId = (mkAttrsId as)
    let pcAttrsIds = map ((++) "pc_" . mkAttrsId) pcs
    let inpcs = "(" ++ concat (intersperse ", " pcAttrsIds) ++ ")"
    putStr "reduc "
    genForAll s as
    putStrLn  ""
    putStr ("confidential_" ++ attrsId ++ "(")
    genUSchema s as
    putStr ") = "
    putStr inpcs
    putStrLn  "."

  ||| Generates the deduction rules that produces PCs
  |||
  ||| Generates rules that permit to deduce PCs from a schema. Their
  ||| should have as many rules as combination of underlying schemas
  ||| (ie, each attribute is either readable `raw` or a variable).
  ||| This produces 2^(length schema) deduction rules, but only rules that
  ||| violate a privacy constraint must be defines.
  |||
  ||| <deducPCs> := <deducPC> ...
  genDeducsPC : Schema -> List PC -> IO ()
  genDeducsPC s pcs = do
    -- Get all pcs deduced by an underlying schema
    let usWithPCs = map (\us => (us, getInnerPCs us pcs)) (powerset s)
    -- Keep only underlying schemas that produce PCs
    let uschemas = filter (isCons . snd) usWithPCs
    let deducPCs = map (uncurry (genDeducPC s)) uschemas
    sequence deducPCs
    putStrLn ""


-- Good! Now, let's generate the code from this information
genPV : List PC -> Eff main [GUARD $ Plain (s @@ ip)] [GUARD cstate] -> IO ()
genPV pcs eff {s} {cstate = (Plain (s' @@ ip))} = prelude s pcs
genPV pcs eff {s} {cstate = (FragV (sl @@ ipl) (sr @@ ipr))} = prelude s pcs

-- instance Handler Guard m where
--     handle (MkPEnv s ip) (Encrypt x a) k = k () (MkPEnv (encrypt a s) ip)
--     handle (MkPEnv s' ip) (Frag ipl ipr s inc) k = k () (MkFEnv ipl ipr s inc)
--     handle (MkPEnv s ip) (Query q) k =
--            let qRes = q (Unit s)
--                qLTy = MkLocTy (qRes @ ip)
--            in k qLTy (MkPEnv s ip)
--     handle (MkFEnv ipl ipr s inc) (QueryL q) k =
--            let qRes = q (Unit (indexing s))
--                qLTy = MkLocTy (qRes @ ipl)
--            in k qLTy (MkFEnv ipl ipr s inc)
--     handle (MkFEnv ipl ipr s inc {s'}) (QueryR q) k =
--            let qRes = q (Unit (indexing (s' \\ s)))
--                qLTy = MkLocTy (qRes @ ipr)
--            in k qLTy (MkFEnv ipl ipr s inc)

instance Handler Guard IO where
    handle (MkPEnv s ip) (Encrypt x a) k =
           do putStrLn "Encrypt"
              k () (MkPEnv (encrypt a s) ip)
    handle (MkPEnv s' ip) (Frag ipl ipr s inc) k =
           do putStrLn "Frag"
              k () (MkFEnv ipl ipr s inc)
    handle (MkPEnv s ip) (Query q) k =
           do putStrLn "Query"
              let q' = q (Unit s)
              k (q' @@ ip) (MkPEnv s ip)
    handle (MkFEnv ipl ipr s inc) (QueryL q) k =
           do putStrLn "QueryL"
              let q' = q (Unit (indexing s))
              k (q' @@ ipl) (MkFEnv ipl ipr s inc)
    handle (MkFEnv ipl ipr s inc {s'}) (QueryR q) k =
           do putStrLn "QueryR"
              let q' = q (Unit (indexing (s' \\ s)))
              k (q' @@ ipr) (MkFEnv ipl ipr s inc)

-- instance Handler Guard List where
--   handle r (Encrypt x y) k = [] -- ?Handler_rhs_2
--   handle r (Frag ipl ipr s inc) k = [] --?Handler_rhs_3
--   handle r (Query q) k = [] --?Handler_rhs_4
--   handle r (QueryL q) k = [] --?Handler_rhs_5
--   handle r (QueryR q) k = [] --?Handler_rhs_6
-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
