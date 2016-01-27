-- module phant.pi
module Main

import guard
import test

import public Effects
import Effect.Random
import Effect.State
import Effect.StdIO

-- %default total

-- Pi language
data PiChan : Type where
  MkPiChan : TTName -> PiChan

data PiVal : Type where
  MkPiVal  : TTName -> PiVal
  -- MkPiValQ : RA s bctx -> List (Expr u bctx) -> PiVal

  -- PiValExpr  : Integer -> Expr u p -> PiVal
  -- PiValQuery : Integer -> RA s p -> PiVal
  PiValPlace : Place -> PiVal

data PiProc : Type where
  PiGet :    PiChan -> PiVal -> PiProc -> PiProc
  PiSend :   PiChan -> PiVal -> PiProc -> PiProc
  PiPar :    PiProc -> PiProc -> PiProc
  PiMkChan : PiVal -> PiProc -> PiProc
  PiBang :   PiProc -> PiProc
  PiEnd :    PiProc


record PiProcs where
  constructor MkPiProcs
  appPi   : PiProc -> PiProc
  alicePi : PiProc -> PiProc
  dbPi    : PiProc -> PiProc
  fragPi  : List (Place, PiProc -> PiProc)

using (n : Nat, a : U, b : U, u : U,
       bctx : Vect n Ctx, bctx' : Vect m Ctx,
       ctx : Vect n Q,
       p : Process, p' : Process, p'' : Process,
       s : Schema, s' : Schema, s'': Schema,
       cs : CState, cs' : CState)

  data Q : Type where
    MkQ : Query u _ -> Q

  instance Show Q where
    show (MkQ q) = show q

  -- data Env : Vect n Q -> Type where
  --   Nil  : Env Nil
  --   (::) : (q : Query u _) -> Env ctx -> Env (MkQ q :: ctx)

  record CTX where
    constructor MkCTX
    -- List of encrypted attributes with their encryption keys
    keys : List (Attribute, Key)
    -- The query before a binding, if any, with the place of the
    -- callee and the query
    query : Maybe (Place, Q)
    -- Environment bind values
    -- env : Vect envSize Q
    env : List (TTName, Q)
    -- PiProcs
    piprocs : PiProcs
    -- Growing index for variable naming
    id : Integer

  -- freshId : Eff Integer [STATE $ CTX n]
  freshId : Eff Integer [STATE CTX]
  freshId = do ctx <- get
               let theId = id ctx
               put $ record { id = theId + 1 } ctx
               pure theId

  -- genPi' : Guard cs cs' bctx (Query u bctx) -> Eff (Query u bctx) [STATE $ CTX n, STDIO]
  genPi' : Guard cs cs' bctx (Query u bctx) -> Eff (Query u bctx) [STATE CTX, STDIO]
  genPi' (Encrypt k a) {bctx}       = do
    ctx <- get
    put $ record { keys = update (a, k) (keys ctx) } ctx
    pure $ defaultQVal UNIT AppP bctx
  genPi' (EncryptF fId k a) {bctx}  = do
    ctx <- get
    put $ record { keys = update (a, k) (keys ctx) } ctx
    pure $ defaultQVal UNIT AppP bctx
  genPi' (Frag sprojs) {bctx} =
    pure $ defaultQVal UNIT AppP bctx
  genPi' (Query q {s}) {bctx}       = do
    -- 1. parse q'. If it involve sending to DB. Look at DB if the
    -- sending is already done or done it.
    ctx <- get
    let q' = q (defaultQVal (SCH s) (AtApp, AtApp, AtDB) bctx)
    put $ record { query = Just (AtDB, MkQ q') } ctx
    pure q'
  genPi' (QueryF fId q {ss}) {bctx} = do
    -- 1. parse q'. If it involve sending to Frag. Look at DB if the
    -- sending is already done or done it.
    ctx <- get
    let s = getSchema fId ss
    let q' = q (defaultQVal (SCH s) (AtApp, AtApp, AtFrag fId) bctx)
    put $ record { query = Just (AtFrag fId, MkQ q') } ctx
    pure q'
  genPi' (Let ttn q g)              = do
      -- FIXME: if `e` involve Alice Data, the let should be done at
      -- Alice place, And Alice should send the result. Actually, I made
      -- the assumption that it is done at App place.
      ctx <- get
      let ctx' = record { env = updateBy ttnEq (ttn, MkQ q) (env ctx) } ctx
      innerQ <- do
                put ctx'
                genPi' g
      -- put ctx
      pure $ downQ innerQ
    where
    -- Si l'innerQ est une QVar et que c'est stop, je dois en faire
    -- une QVar_. Si c'est Pop, je dépile. Si c'est autre chose, je
    -- laisse allé.
    downQ : Query u (z :: bctx) -> Query u bctx
    downQ (QVar Stop) {z=(u,ttn,ppp)} {bctx} = QVar_ ttn u ppp {bctx}
    downQ (QVar (Pop prf)) {bctx}            = QVar prf {bctx}
    downQ q                                  = really_believe_me q
    -- downQ (QVal x y) {bctx} = QVal x y {bctx}
    -- downQ (QVar_ x y z) {bctx} = QVar_ x y z {bctx}
    -- downQ (QPrivy x) {bctx} = QPrivy (downQ x)
    -- downQ (QEq x y) = QEq (downQ x) (downQ y)
    -- downQ (QElem x xs) = QElem (downQ x) (downQ xs)
    -- downQ (QProject sproj x) = QProject sproj (downQ x)
    -- downQ (QSelect a p x) = QSelect a p (downQ x)
    -- downQ (QCount scount x) = ?getQ_rhs_8
    -- downQ (QProduct x y) = ?getQ_rhs_9
  genPi' (Pure x) = pure x
  genPi' (SeqApp Privy g)           = do
    e <- genPi' g
    pure (QPrivy e)
  genPi' (Bind x f)                 = do
      -- J'ajoute q dans le context, puis j'en fais une var.
      q   <- genPi' x
      id  <- freshId
      ctx <- get
      let ttn = UN $ "var_" ++ show id
      let qvar = QVar_ ttn (getU q) (getProcess q)
      -- Add new variable into the context
      put $ record { env = updateBy ttnEq (ttn, MkQ q) (env ctx) } ctx
      -- FIXME: Ici, c'est forcement une query retourné par un Query
      -- ou en let. Si, c'est par un let, la QVar_ existe déjà! ça ne
      -- sert a rien de l'ajouter.
      genPi' (f qvar)

  genPi : Guard (Plain s) cs' [] (Query u []) -> IO ()
  -- genPi g {cs' = (Plain xs)} {s} {u} = let
  --   expr = the (IO (Query u _)) $
  --          runInit [(MkCTX [])]
  -- genPi g {cs' = (FragV xs)} {s} {u} = ?genPi_rhs_2
  genPi g {s} {u} =
    let keys_ = the (List ((String, U), String)) []
        query_ = the (Maybe (Place,Q)) Nothing
        -- env = the (Vect Z Q) []
        env_ = the (List (TTName, Q)) []
        piprocs_ = MkPiProcs (\k => PiEnd) (\k => PiEnd) (\k => PiEnd) Nil
        id_ = 0
    in runInit [(MkCTX keys_ query_ env_ piprocs_ id_), ()] $ do
          q   <- genPi' g
          ctx <- get
          -- Now update piprocs (from ctx) with q and update it
          let env_ = CTX.env ctx
          putStr $ show env_

  -- lala : Guard (Plain s) cs' [] (Query a []) -> IO ()
  -- lala g = genPi g

main : IO ()
main = genPi (do placesF_2Let
                 placesF_3Let
                 meetingFDo' (encrypt "mykey" "toto"))

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
