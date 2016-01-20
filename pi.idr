module phant.pi

import guard
import ra

import public Effects
import Effect.Random
import Effect.State
import Effect.StdIO

%default total

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

using (bctx : Vect n Ctx)
  data Q : Type where
    MkQ : RA s bctx -> Q

  record CTX where
    constructor MkCTX
    -- List of encrypted attributes with their encryption keys
    keys : List (Attribute, Key)
    -- The query before a binding, if any, with the place of the
    -- callee and the query
    query : Maybe (Place, Q)
    -- Growing index for variable naming
    id : Integer

  freshId : Eff Integer [STATE CTX]
  freshId = do ctx <- get
               let theId = id ctx
               put $ record { id = theId + 1 } ctx
               pure theId


  mkVar : Expr u bctx -> Eff (Expr u bctx) [STATE CTX]
  mkVar e @ (ExprVar' _ _)  = pure e
  mkVar e @ (ExprVar _ n _) = pure (ExprVar' n e)
  mkVar e                   = do id <- freshId
                                 let name = "var_" ++ show id
                                 pure (ExprVar' name e)

  PiProcs : Type
  PiProcs = List (Place, (PiProc -> PiProc))

  genPi' : Guard cs cs' bctx (Expr b bctx) ->
           Eff (Expr b bctx) [STATE CTX, STDIO]
  genPi' (Encrypt k a) {bctx}       = do
    ctx <- get
    put  $ record { keys = update (a, k) (keys ctx) } ctx
    pure $ defaultExprVal UNIT bctx AppP
  genPi' (EncryptF fId k a) {bctx}  = do
    ctx <- get
    put  $ record { keys = update (a, k) (keys ctx) } ctx
    pure $ defaultExprVal UNIT bctx AppP
  genPi' (Frag sprojs) {bctx} =
    pure $ defaultExprVal UNIT bctx AppP
  genPi' (Query q {s}) {bctx}       = do
    -- 1. parse q. If it involve sending to DB. Look at DB if the
    -- sending is already done or done it.
    ctx <- get
    let q' = q (Unit s)
    put  $ record { query = Just (AtDB, MkQ q') } ctx
    pure $ defaultExprVal (SCH $ getSchema q')
                          bctx
                          (AtApp, AtApp, AtDB)
  genPi' (QueryF fId q {ss}) {bctx} = do
    -- 1. parse q. If it involve sending to Frag. Look at DB if the
    -- sending is already done or done it.
    ctx <- get
    let s = getSchema fId ss
    let q' = q (Unit s)
    put  $ record { query = Just (AtFrag fId, MkQ q') } ctx
    pure $ defaultExprVal (SCH $ getSchema q')
                          bctx
                          (AtApp, AtApp, AtFrag fId)
  genPi' (Let ttn e g)              = do
    -- FIXME: if `e` involve Alice Data, the let should be done at
    -- Alice place, And Alice should send the result. Actually, I made
    -- the assumption that it is done at App place.
    ctx <- get
    innerE <- genPi' g
    ?mlkj

  genPi' (Pure x) = pure x
  genPi' (SeqApp Privy g)           = do
    e <- genPi' g
    pure (ExprPrivy e)
  genPi' (Bind x f)                 = do
    e <-  genPi' x
    genPi' (f !(mkVar e))

  genPi : Guard (Plain s) cs' [] (Expr a []) -> IO ()
  genPi g {s} {a} = let
      expr = the (IO (Expr a _)) $
             runInit [(MkCTX [] Nothing 0), ()] $
             genPi' g
    in print ""

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
