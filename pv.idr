module phant.pv

import guard
import pi

import Effects
import Control.Monad.State

%access public
%default total

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

||| Makes a tuple from a schema.
|||
||| Each element of the tuple is transform as an attribute identifier.
||| The Id and Count attribute are removed.
mkTuple : Schema -> String
mkTuple s = let s' = delete Count (delete Id s)
            in "(" ++ concat (intersperse "," (map mkAttrId s')) ++ ")"

-- ||| Generates a forall term.
-- |||
-- ||| <forall> := forall <attrVId>: attribute, ...;
-- |||
-- ||| This generates the forall term for a list of attributes. The
-- ||| generation uses the original schema and produce a varialble for
-- ||| each missing attribute. If the original schema and the list of
-- ||| attributes are equivalent, then no forall term is produced.
-- |||
-- ||| @ s  The original schema.
-- ||| @ as The list of attributes targeting the forall.
-- genForAll : (s : Schema) -> (as : List Attribute) -> IO ()
-- genForAll s as with (s \\ as)
--   genForAll s as | []  = putStr "" -- no forall
--   genForAll s as | out = do        -- forall
--     let attrVIds = map (flip (++) ": attribute" . mkAttrVId) out
--     putStr "forall "
--     putStr $ concat (intersperse ", " attrVIds)
--     putStr ";"

-- genSchema : (s : Schema) -> (us : List Attribute) -> (k : Maybe Key) -> IO ()
-- genSchema s us k = do
--     let attrs = map (\a => case elem a us of
--                              True  => case isEncrypted a of
--                                         True  => mkAttId a k
--                                         False => mkAttId a Nothing
--                              False => "unit") s
--     putStr $ "(" ++ concat (intersperse ", " attrs) ++ ")"
--   where
--   mkAttId : Attribute -> Maybe Key -> String
--   mkAttId a Nothing  = mkRawAttId a
--   mkAttId a (Just k) = "senc(" ++ mkAttrId a ++ ", " ++ k ++ ")"

-- ||| Generate an underlying schema.
-- |||
-- ||| Generate an underlying schema based on the original one. If an
-- ||| attribute of `s` is in `us` then it produces a readable attribute
-- ||| (raw). Otherwise it produces a variable attribute.
-- |||
-- ||| <uschema> := (<attr>, ...)
-- ||| <attr>    := <rawAttrId> | <attrVId>
-- |||
-- ||| @ s  the original schema
-- ||| @ us the underlying schema
-- genUSchema : (s : Schema) -> (us : List Attribute) -> IO ()
-- genUSchema s us = do
--   let attrs = map (\a => case elem a us of
--                            True  => mkRawAttId a
--                            False => mkAttrVId a) s
--   putStr $ "(" ++ (concat (intersperse ", " attrs)) ++ ")"

-- ||| Generates the preamble of a ProVerif file.
-- |||
-- ||| @ s   The list of attributes considered in this system.
-- ||| @ pcs The list of privacy constraints.
-- preamble : (s : Schema) -> (pcs : List PC) -> IO ()
-- preamble s pcs = do
--     genDefault
--     putStrLn "(* ----------------------------------------------- DB attribute and PC *)"
--     putStrLn "(* Database attributes *)"
--     genDbAttrs s
--     putStrLn "(* Privacy constraints -- Attacker *)"
--     genAttacker pcs
--     putStrLn "(* Instruction for an attacker: what is a PC *)"
--     genDeducsPC s pcs
--     putStrLn "(* ----------------------------------------------------- DB Operations *)"
--     putStrLn "(* Projections *)"
--     putStrLn "(* Selections *)"
--     putStrLn "(* Grouping *)"
--     putStrLn "(* Aggregation *)"
--     putStrLn "(* -------------------------------------------------------------- Main *)"

--   where
--   genDefault : IO ()
--   genDefault = putStrLn $
--     unlines [
--       "set ignoreTypes = false.",
--       "(* set traceDisplay = long. *)",
--       "",
--       "(* Debug: test if reduction rules applied correctly *)",
--       "event NO_RULE.",
--       "query event(NO_RULE).",
--       "",
--       "(* Attribute of the database *)",
--       "type attribute.",
--       "const unit: attribute.  (* unit: attribute without information *)",
--       "fun raw(bitstring): attribute [data]. (* raw: constructor for attribute  *)",
--       "(* A raw is labelised by its position in the schema *)",
--       "",
--       "(* ------------------------------------------------ Privacy Operations *)",
--       "(* Defragmentation *)",
--       "reduc forall vd: attribute, vn: attribute, va: attribute;",
--       "defrag((vd,unit,unit), (unit,vn,va)) = (vd,vn,va).",
--       "",
--       "(* Symmetric Encryption *)",
--       "type skey.",
--       "fun senc(bitstring, skey): attribute.",
--       "reduc forall m: bitstring, sk: skey; sdec(senc(m, sk), sk) = raw(m).",
--       "",
--       "(* Homomorphic Encryption *)",
--       "type pkey.",
--       "fun pk(skey): pkey.",
--       "fun henc(bitstring, pkey): attribute.",
--       "reduc forall m: bitstring, sk: skey; hdec(henc(m, pk(sk)), sk) = raw(m).",
--       ""]

--   ||| Generate the database attributes.
--   ||| <dbAttr> := const <attrId>: bitstring [private]. ...
--   genDbAttrs : List Attribute -> IO ()
--   genDbAttrs as = do
--     let dbAttrs = map (\a => "const "
--                              ++ (mkAttrId a)
--                              ++ ": bitstring [private].") as
--     sequence (map putStrLn dbAttrs)
--     putStrLn ""

--   ||| Generate the attacker model.
--   ||| <attack> := <const> ...
--   |||             <query> ...
--   ||| <const>  := const pc_<attrsId>: bistring [private].
--   ||| <query>  := query attacker(pc_<attrsId>).
--   genAttacker : List PC -> IO ()
--   genAttacker pcs = do
--     let pcAttrsIds = map  ((++) "pc_" . mkAttrsId) pcs
--     let consts = map (\id => "const " ++ id ++ ": bitstring [private].")
--                      pcAttrsIds
--     let querys = map (\id => "query attackers(" ++ id ++ ").")
--                      pcAttrsIds
--     sequence (map putStrLn consts)
--     putStrLn ""
--     sequence (map putStrLn querys)
--     putStrLn ""


--   ||| Generates the deduction rules that produces PCs
--   |||
--   ||| <deducPC> := reduc <forall>
--   |||              confidential_<attrsId>(<uschema>) = <inpcs>.
--   ||| <inpcs>   := (pc_<attrsId>, ...)
--   genDeducPC : Schema -> List Attribute -> List PC -> IO ()
--   genDeducPC s as []  = putStr ""
--   genDeducPC s as pcs = do
--     let attrsId = (mkAttrsId as)
--     let pcAttrsIds = map ((++) "pc_" . mkAttrsId) pcs
--     let inpcs = "(" ++ concat (intersperse ", " pcAttrsIds) ++ ")"
--     putStr "reduc "
--     genForAll s as
--     putStrLn  ""
--     putStr ("confidential_" ++ attrsId ++ "(")
--     genUSchema s as
--     putStr ") = "
--     putStr inpcs
--     putStrLn  "."

--   ||| Generates the deduction rules that produces PCs
--   |||
--   ||| Generates rules that permit to deduce PCs from a schema. Their
--   ||| should have as many rules as combination of underlying schemas
--   ||| (ie, each attribute is either readable `raw` or a variable).
--   ||| This produces 2^(length schema) deduction rules, but only rules that
--   ||| violate a privacy constraint must be defines.
--   |||
--   ||| <deducPCs> := <deducPC> ...
--   genDeducsPC : Schema -> List PC -> IO ()
--   genDeducsPC s pcs = do
--     -- Get all pcs deduced by an underlying schema
--     let usWithPCs = map (\us => (us, getInnerPCs us pcs)) (powerset s)
--     -- Keep only underlying schemas that produce PCs
--     let uschemas  = filter (isCons . snd) usWithPCs
--     let deducPCs  = map (uncurry (genDeducPC s)) uschemas
--     sequence deducPCs
--     putStrLn ""

record PiProcs (fragsNumber : Nat) where
  constructor MkPiProcs
  appPi   : PiProc -> PiProc
  alicePi : PiProc -> PiProc
  dbPi    : PiProc -> PiProc
  fragPi  : Vect fragsNumber (PiProc -> PiProc)
  id      : Integer

fragsNumber : PiProcs n -> Nat
fragsNumber _ {n} = n

||| Generate a fresh identifier from the Piprocs.
freshId : PiProcs n -> PiProcs n
freshId pips = record { id = 1 + (id pips) } pips

||| Sets the PiProc for a specific place.
setPiProcs : Place -> (PiProc -> PiProc) -> PiProcs n -> PiProcs n
setPiProcs Alice             pi pips        = record {
             alicePi = \k => (alicePi pips) $ pi k } pips
setPiProcs App               pi pips        = record {
             appPi = \k => (appPi pips) $ pi k } pips
setPiProcs DB                pi pips        = record {
             dbPi = \k => (dbPi pips) $ pi k } pips
setPiProcs (Frag fId {n=n1}) pi pips {n=n2} = record {
             fragPi =
               let frags = fragPi pips
                   -- FIXME: give the proof that fragNums == pipFNums.
                   -- I'm sure about that since the Frag combinator is
                   -- applicable only once in the computation. And my
                   -- function that construct the pips is based on
                   -- that combinator.
                   fId'  = prim__believe_me (Fin n1) (Fin n2) fId
                   frag  = \k => (index fId' frags) $ pi k
               in replaceAt fId' frag frags } pips

-- Make a pi proc that receive an expression. If the expression
-- contains sub expressions with different (callee/recipient) then
-- generate the receiver for those two.
piProcFromExpr : Expr u p -> Process -> PiProcs n -> PiProcs n
-- Expr/0
piProcFromExpr ExprUNIT op pips = ?piProcFromExpr_rhs_2
piProcFromExpr (ExprNAT k) op pips = ?piProcFromExpr_rhs_3
piProcFromExpr (ExprTEXT s) op pips = ?piProcFromExpr_rhs_4
piProcFromExpr (ExprREAL d) op pips = ?piProcFromExpr_rhs_5
piProcFromExpr (ExprBOOL b) op pips = ?piProcFromExpr_rhs_6
piProcFromExpr (ExprCRYPT x) op pips = ?piProcFromExpr_rhs_7
piProcFromExpr (ExprSCH s p) op pips = ?piProcFromExpr_rhs_8
-- Expr/1
piProcFromExpr (ExprPutP p e) op pips = ?piProcFromExpr_rhs_18
piProcFromExpr (ExprNot e) op pips = ?piProcFromExpr_rhs_12
-- Expr/2
piProcFromExpr (ExprEq x y) op pips = ?piProcFromExpr_rhs_9
piProcFromExpr (ExprGtEq x y) op pips = ?piProcFromExpr_rhs_10
piProcFromExpr (ExprElem x y) op pips = ?piProcFromExpr_rhs_11
-- Expr_SQL
piProcFromExpr (ExprUnion x y) op pips = ?piProcFromExpr_rhs_13
piProcFromExpr (ExprProduct x y) op pips = ?piProcFromExpr_rhs_14
piProcFromExpr (ExprProject sproj x) op pips = ?piProcFromExpr_rhs_15
piProcFromExpr (ExprDrop sproj x) op pips = ?piProcFromExpr_rhs_16
piProcFromExpr (ExprCount scount x) op pips = ?piProcFromExpr_rhs_17

||| Generates the piproc for a query.
|||
||| First parse inner expression then produces those two:
||| - @Caller_Q : -Callee_Q(q)-
||| - @Callee_Q : Callee_Q(q)
|||
||| @ q The query.
piProcFromQ : (q : RA s p) -> PiProcs n -> PiProcs n
piProcFromQ q pips {p = (rc, cr, ce)} = let
    pips1 = piProcFromQ' q pips
    pips2 = freshId pips1
    pips3 = setPiProcs cr (PiSend (PiValPlace ce)
                                  (PiValQuery (id pips2) q)) pips2
    pips4 = setPiProcs ce (PiGet  (PiValPlace ce)
                                  (PiValQuery (id pips2) q)) pips3
    in pips4
  where
  piProcFromQ' : (RA s p') -> PiProcs n -> PiProcs n
  piProcFromQ' (Project sproj q) pips      = piProcFromQ' q pips
  piProcFromQ' (Select a pred q) {p'} pips =
                 let e = pred (defaultExpr (getU a) p')
                 in piProcFromExpr e p' pips
  piProcFromQ' (Count scount q) pips       = piProcFromQ' q pips
  piProcFromQ' (Unit s p') pips            = pips

instance MonadState (Schema,
                     List (Attribute, Key),
                     PiProcs pipFNums) m => Handler Guard m where
    handle (MkPEnv s) (Encrypt x a) k                               = do
      -- Note: Encrypt are stackable, so I should use a stack to
      -- manage key per attribute in the `ks`. General algorithm is
      -- stack a key on encrypt and unstack key on decrypt. But, for
      -- now, I don't have decrypt combinator. So erasing previous key
      -- with `update` is OK.
      (os, ks, pips) <- get
      let skey = x ++ "_skey"
      put ((encrypt a os), update (a, skey) ks, pips)
      -- continuation
      k () (MkPEnv (encrypt a s))
    handle (MkFEnv ss {n}) (EncryptF fId x a) k                     = do
      (os, ks, pips) <- get
      let skey = x ++ "_skey"
      put ((encrypt a os), update (a, skey)  ks, pips)
      -- continuation
      k () (MkFEnv (encryptF a fId ss))
    handle (MkPEnv s) (Frag sprojs) k                               = do
      -- continuation
      k () (MkFEnv (frag sprojs s))
    handle (MkPEnv s) (Query q {p}) k                               = do
      (os, ks, pips) <- get
      let q' = q (Unit s p)
      -- pips of pi expr
      let pips' = piProcFromQ q' pips
      put (os, ks, pips')
      -- continuation
      k (ExprSCH (getSchema q') p) (MkPEnv s)
    handle (MkFEnv ss {n=fragNums}) (QueryF fId q {p}) k {pipFNums} = do
      (os, ks, pips) <- get
      let s = (getSchema fId ss)
      let q' = q (Unit s p)
      -- let frags = fragPi pips
      -- let fId' = prim__believe_me (Fin fragNums) (Fin pipFNums) fId
      -- let f = index fId' frags
      -- construction of pi expr
      let pips' = piProcFromQ q' pips
      put (os, ks, pips')
      -- continuation
      k (ExprSCH (getSchema q') p) (MkFEnv ss)

genPV : Eff a [GUARD $ Plain s] [GUARD cstate] -> IO ()
genPV eff {s} {a} {cstate = Plain s'} = do
  let body = the (State (Schema, List (Attribute, Key), PiProcs Z) a) $
             runInit [MkPEnv s] eff
  let initPiProcs = (MkPiProcs (\k => PiEnd)
                               (\k => PiEnd)
                               (\k => PiEnd)
                               Nil 0 {fragsNumber=Z})
  let (a,s) = runState body (s, [], initPiProcs)
  return ()
genPV eff {s} {a} {cstate = FragV frags} = do
  -- preamble s pcs
  -- the (StateT Integer IO a) $ runInit [MkPEnv s ip] eff
  -- scId <- schema s'
  -- let body = the (StateT (Schema, Maybe Key) IO a) $ runInit [MkPEnv s] eff
  let body = the (State (Schema, List (Attribute, Key), PiProcs (length frags)) a) $
             runInit [MkPEnv s] eff
  let initPiProcs = (MkPiProcs (\k => PiEnd)
                               (\k => PiEnd)
                               (\k => PiEnd)
                               (replicate (length frags) (\k => PiEnd)) 0)
  let (a,s) = runState body (s, [], initPiProcs)
  return ()

-- genRA : RA s -> Schema -> Maybe Key -> IO ()
-- genRA (Union x y)      ts k = do
--   putStrLn "union("
--   genRA x ts k
--   genRA y ts k
--   putStrLn ")"
-- genRA (Diff x y)       ts k = do
--   putStrLn "diff("
--   genRA x ts k
--   genRA y ts k
--   putStrLn ")"
-- genRA (Product x y)    ts k = do
--   putStrLn "product("
--   genRA x ts k
--   genRA y ts k
--   putStrLn ")"
-- genRA (Project s' x)   ts k = do
--   let attrs = mkTuple s'
--   putStrLn $ "proj(" ++ attrs ++ ","
--   genRA x ts k
--   putStrLn ")"
-- genRA (Select a q x) {s} ts k = do
--   -- FIXME: mkTuple should use something around `q`
--   let attrs = mkTuple [a]
--   putStrLn $ "select(" ++ attrs ++ ","
--   genRA x ts k
--   putStrLn ")"
-- genRA (Drop s' x)      ts k = do
--   let attrs = mkTuple s'
--   putStrLn $ "drop(" ++ attrs ++ ","
--   genRA x ts k
--   putStrLn ")"
-- genRA (Count scount x) ts k = do
--   let attrs = mkTuple scount
--   putStrLn $ "count(" ++ attrs ++ ","
--   genRA x ts k
--   putStrLn ")"
-- genRA (Unit s ) ts k = genSchema ts s k

-- instance Handler Guard (StateT (Schema, Maybe Key) IO) where
--     handle (MkPEnv s) (Encrypt x a) k            = do
--       let skey = x ++ "_sk"
--       (ts, _) <- get
--       put ((encrypt a ts), Just skey)
--       lift $ putStrLn $ "const " ++ skey ++ ": skey [private]."
--       lift $ putStrLn ""
--       k () (MkPEnv (encrypt a s))
--     handle (MkPEnv s) (Frag s') k    = do
--       k () (MkFEnv s')
--     handle (MkPEnv s) (Query q) k                = do
--       (ts, skey) <- get
--       lift $ putStrLn $ "let " ++ "lala" ++ "(request: channel) ="
--       lift $ putStrLn "  in (request, to: channel);"
--       lift $ putStrLn "  let res = "
--       let q' = q (Unit s)
--       lift $ genRA q' ts skey
--       lift $ putStrLn "  in"
--       lift $ putStrLn $ "out (to, res)."
--       -- Note: operational will return a filled list. Here we don't
--       -- care.
--       k (ExprSCH (getSchema q')) (MkPEnv s)
--     handle (MkFEnv sproj {s}) (QueryL q) k      = do
--       let fl = fst (frag sproj s)
--       lift $ putStrLn "QueryL"
--       let q' = q (Unit fl)
--       k (ExprSCH (getSchema q')) (MkFEnv sproj)
--     handle (MkFEnv sproj {s}) (QueryR q) k = do
--       let fr = snd (frag sproj s)
--       lift $ putStrLn "QueryR"
--       let q' = q (Unit fr)
--       k (ExprSCH (getSchema q')) (MkFEnv sproj)


-- -- Can I get the list of attribute, the state of the cloud and the
-- -- list of pc, from a Guard effect ? Yes for the list of attribute and
-- -- the cloud state :
-- --
-- -- > testPV : Eff r [GUARD $ Plain $ s@@ip] [GUARD $ FragV (sl@@ipl) (sr@@ipr)] -> (Schema, CState, List Schema)
-- -- > testPV x {s} {sl} {ipl} {sr} {ipr} = (s, FragV (sl @@ ipl) (sr @@ ipr), [])
-- --
-- -- If I take the list of attribute in arguments, then I can generate
-- -- all the first part of the file. Let's do this, but first define
-- -- what is a list of pc:
-- --
-- --
-- -- The preamble of a pv file should look like something like this
-- genPV : List PC -> Eff a [GUARD $ Plain s] [GUARD cstate] -> IO ()
-- -- genPV pcs eff {s} {cstate = (FragV (sl @@ ipl) (sr @@ ipr))} = preamble s pcs
-- genPV pcs eff {s} {a} {- cstate = (Plain (s' @@ ip)) -} = do
--   preamble s pcs
--   -- the (StateT Integer IO a) $ runInit [MkPEnv s ip] eff
--   -- scId <- schema s'
--   let body = the (StateT (Schema, Maybe Key) IO a) $ runInit [MkPEnv s] eff
--   runStateT body (s, Nothing)
--   return ()


-- -- Good! Now, let's generate the code from this information
-- genPV : List PC -> Eff a [GUARD $ Plain (s @@ ip)] [GUARD cstate] -> IO ()
-- genPV pcs eff {s} {ip} {a} {- cstate = (Plain (s' @@ ip)) -} = do
--   -- preamble s pcs
--   -- the (StateT Integer IO a) $ runInit [MkPEnv s ip] eff
--   -- scId <- schema s'
--   let val = the (StateT Integer IO a) $ runInit [MkPEnv s ip] eff
--   let val' = runStateT val 1
--   val'
--   return ()

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
