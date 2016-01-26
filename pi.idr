module phant.pi

import guard
import test

import public Effects
import Effect.Random
import Effect.State
import Effect.StdIO

%default total

-- Pi language
data PiChan : Type where
  MkPiChan : TTName -> PiChan

data PiVal : Type where
  MkPiVal  : TTName -> PiVal
  -- MkPiValQ : RA s bctx -> List (Expr u bctx) -> PiVal

  PiValExpr  : Integer -> Expr u p -> PiVal
  PiValQuery : Integer -> RA s p -> PiVal
  PiValPlace : Place -> PiVal

data PiProc : Type where
  PiGet :    PiChan -> PiVal -> PiProc -> PiProc
  PiSend :   PiChan -> PiVal -> PiProc -> PiProc
  PiPar :    PiProc -> PiProc -> PiProc
  PiMkChan : PiVal -> PiProc -> PiProc
  PiBang :   PiProc -> PiProc
  PiEnd :    PiProc


-- record PiProcs where
--   constructor MkPiProcs
--   appPi   : PiProc -> PiProc
--   alicePi : PiProc -> PiProc
--   dbPi    : PiProc -> PiProc
--   fragPi  : List (PiProc -> PiProc)

using (bctx : Vect n Ctx)
  data Q : Type where
    MkQ : RA s _ -> Q

  -- data Env : Vect n (U, Process, TTName) -> Type where
  --   Nil  : Env Nil
  --   (::) : (el u) -> Env bctx -> Env ()

  record CTX (size : Nat)  where
    constructor MkCTX
    -- List of encrypted attributes with their encryption keys
    keys : List (Attribute, Key)
    -- The query before a binding, if any, with the place of the
    -- callee and the query
    query : Maybe (Place, Q)
    --
    osef : Vect size ()
    -- Growing index for variable naming
    id : Integer

  addOsef : () -> CTX n -> CTX (S n)
  addOsef u r = MkCTX (keys r) (query r) (u :: osef r) (id r)

  freshId : Eff Integer [STATE $ CTX n]
  freshId = do ctx <- get
               let theId = id ctx
               put $ record { id = theId + 1 } ctx
               pure theId


  mkVar : {bctx : Vect n Ctx} -> Expr u bctx -> Eff (Expr u bctx) [STATE $ CTX n]
  mkVar e @ (ExprVar _ _)  = pure e
  -- FIXME: use the context to unbind the let and bind the var
  mkVar e @ (ExprLetVar _ n _) = pure (ExprVar n e)
  mkVar e                   = do id <- freshId
                                 let name = "var_" ++ show id
                                 pure (ExprVar name e)

  PiProcs : Type
  PiProcs = List (Place, (PiProc -> PiProc))

  genPi' : {bctx : Vect n Ctx} -> Guard cs cs' bctx (Expr b bctx) ->
           Eff (Expr b bctx) [STATE $ CTX n, STDIO]
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
    let ctx' = addOsef () ctx
    innerE <- do
              putM ctx'
              genPi' g
    putM ctx
    ?mlkjk
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
             runInit [(MkCTX [] Nothing [] 0), ()] $
             genPi' g
    in print ""

  -- lala : Guard (Plain s) cs' [] (Expr a []) -> String
  -- lala g = show g

  -- lala' : String
  -- lala' = lala meetings

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
