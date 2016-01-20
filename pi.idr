module phant.pi

import guard
import ra

import public Effects
import Effect.Random
import Effect.State
import Effect.StdIO

-- Pi language
data PiVal : Type where
  PiValExpr  : Integer -> Expr u p -> PiVal
  PiValQuery : Integer -> RA s p -> PiVal
  PiValPlace : Place -> PiVal

data PiProc : Type where
  PiGet :    PiVal -> PiVal -> PiProc -> PiProc
  PiSend :   PiVal -> PiVal -> PiProc -> PiProc
  PiPar :    PiProc -> PiProc -> PiProc
  PiMkChan : PiVal -> PiProc -> PiProc
  PiBang :   PiProc -> PiProc
  PiEnd :    PiProc


-- record PiProcs (fragsNumber : Nat) where
--   constructor MkPiProcs
--   appPi   : PiProc -> PiProc
--   alicePi : PiProc -> PiProc
--   dbPi    : PiProc -> PiProc
--   fragPi  : Vect fragsNumber (PiProc -> PiProc)

-- fragsNumber : PiProcs n -> Nat
-- fragsNumber _ {n} = n

upper : Integer
upper = 10000

using (bctx : Vect n Ctx)
  mkVar : Expr u bctx -> Eff (Expr u bctx) [RND]
  mkVar e@(ExprVar' _ _) = pure e
  mkVar e@(ExprVar _ name _) = pure (ExprVar' name e)
  mkVar e = do
    let name = "var_" ++ show !(rndInt 0 upper)
    pure (ExprVar' name e)
  -- mkVar e@(ExprVal _ _) {bctx=[]} = do
  --   let name = "var_" ++ show !(rndInt 0 upper)
  --   pure (ExprVar' name e)

  PiProcs : Type
  PiProcs = List (Place, (PiProc -> PiProc))

  data Q : Type where
    MkQ : RA s bctx -> Q

  record CTX where
    constructor MkCTX
    -- List of encrypted attributes with their encryption keys
    keys : List (Attribute, Key)
    -- The query before a binding, if any, with the place of the callee
    -- and the query
    query : Maybe (Place, Q)
    -- Is the query private?
    privy : Bool

  genPi' : Guard cs cs' bctx (Expr b bctx) -> Eff (Expr b bctx) [STATE CTX, RND, STDIO]
  genPi' (Encrypt k a) {bctx} = do
    ctx <- get
    put $ record { keys = update (a, k) (keys ctx) } ctx
    pure (ExprVal AppP () {bctx})
  genPi' (EncryptF fId k a) {bctx} = do
    ctx <- get
    put $ record { keys = update (a, k) (keys ctx) } ctx
    pure (ExprVal AppP () {bctx})
  genPi' (Frag sprojs) {bctx} =
    pure (ExprVal AppP () {bctx})
  genPi' (Query q {s}) {bctx} = do
    -- 1. parse q. If it involve sending to DB. Look at DB if the
    -- sending is already done or done it.
    ctx <- get
    let q' = q (Unit s)
    put $ record { query = Just (AtDB, MkQ q') } ctx
    pure (ExprVal {u=SCH $ getSchema q'} {bctx} (AtApp,AtApp,AtDB) [])
  -- genPi' (QueryF fId q {ss}) = do
  --   -- 1. parse q. If it involve sending to Frag. Look at DB if the
  --   -- sending is already done or done it.
  --   ctx <- get
  --   let s = getSchema fId ss
  --   let q' = q (Unit s)
  --   put $ record { query = Just (AtFrag fId, MkQ q') } ctx
  --   pure []
  -- genPi' Privy = do
  --   -- TODO: remove privy in record. Privy is useless since the expr
  --   -- will be well typed thanks to the SeqApp.
  --   ctx <- get
  --   put $ record { privy = True } ctx
  --   pure []
  -- genPi' (Let ttn e x) = do
  --   -- FIXME: if `e` involve Alice Data, the let should be done at
  --   -- Alice place, And Alice should send the result. Actually, I made
  --   -- the assumption that it is done at App place.
  --   ?genPi'_rhs_7
  -- genPi' (Map m x) = ?genPi'_rhs_8
  -- genPi' (Pure x) = ?genPi'_rhs_9
  genPi' (SeqApp Privy g) = do
    e <- genPi' g
    pure $ ExprPrivy e
  genPi' (Bind x f) = do
    e <-  genPi' x
    ?genPi'_rhs_11

  genPi : Guard (Plain s) cs' bctx (Expr a bctx) -> IO ()
  genPi g {s} {a} {bctx} = let expr = the (IO (Expr a bctx)) $
                                 runInit [(MkCTX [] Nothing False), 0, ()] $
                                 genPi' g
                           in print ""

  -- inter : Guard cs cs' bnj e -> Eff e [RND]
  -- inter (Encrypt k a) = ?inter_rhs_1
  -- inter (EncryptF fId k a) = ?inter_rhs_2
  -- inter (Frag sprojs) = ?inter_rhs_3
  -- inter (Query q) = ?inter_rhs_4
  -- inter (QueryF fId q) = ?inter_rhs_5
  -- inter Privy = pure (ExprPrivy)
  -- inter (Let t e x) = ?inter_rhs_7
  -- inter (Pure x) = ?inter_rhs_8
  -- inter (SeqApp x y) = ?inter_rhs_9
  -- inter (Bind x f) = do e <- inter x
  --                       rnd <- rndInt 0 upper
  --                       let name = "var_" ++ show rnd
  --                       inter (f (ExprVar' (UN name) e))

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
