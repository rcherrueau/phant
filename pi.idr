-- module phant.pi
module Main

import guard
import test

import public Effects
import Effect.Random
import Effect.State
import Effect.StdIO
-- import Debug.Trace

-- %default total

-- Pi language
data PiChan : Type where
  MkPiChan : Place -> PiChan

instance Show PiChan where
  show (MkPiChan p) = "(πc " ++ show p ++ ")"

data PiVal : Type where
  MkPiVal : Query u bctx -> PiVal

instance Show PiVal where
  show (MkPiVal q) = "(πv " ++ show q ++ ")"

data PiProc : Type where
  PiSend :   (ce : PiChan) -> (rc : PiChan) -> PiVal -> PiProc -> PiProc
  PiGet :    PiChan -> PiVal -> PiProc -> PiProc
  -- PiPar :    PiProc -> PiProc -> PiProc
  -- PiBang :   PiProc -> PiProc
  PiEnd :    PiProc

instance Show PiProc where
  show (PiSend x y z pi) =
    "(π! " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ") . " ++ show pi
  show (PiGet x y pi) =
    "(π? " ++ show x ++ " " ++ show y ++ ") . " ++ show pi
  show PiEnd = "0"


record PiProcs where
  constructor MkPiProcs
  appPi   : PiProc -> PiProc
  alicePi : PiProc -> PiProc
  dbPi    : PiProc -> PiProc
  fragsPi : List (Place, PiProc -> PiProc)

instance Show PiProcs where
    show (MkPiProcs appPi alicePi dbPi fragsPi) =
      show "App: " ++ show (appPi PiEnd) ++ "\n" ++
      show "Alice: " ++ show (alicePi PiEnd) ++ "\n" ++
      show "DB: " ++ show (dbPi PiEnd) ++ "\n" ++
      unlines (map (\((AtFrag fId), fpi) =>
        "Frag" ++ (show $ finToNat fId) ++ ": " ++
        show (fpi PiEnd)) fragsPi)

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

  record CTX where
    constructor MkCTX
    -- List of encrypted attributes with their encryption keys
    keys : List (Attribute, Key)
    -- The query before a binding, if any, with the place of the
    -- callee of a query
    callee : Maybe Place
    -- Environment bind values
    -- env : Vect envSize Q
    env : List (TTName, Q)
    -- PiProcs
    piprocs : PiProcs
    -- Growing index for variable naming
    id : Integer

  freshId : Eff Integer [STATE CTX]
  freshId = do ctx <- get
               let theId = id ctx
               put $ record { id = theId + 1 } ctx
               pure theId

  -- and a q inside the environment at a `ttn` places. If `ttn`
  -- already exist, this will create a fresh one and return it.
  addEnv : Query u bctx -> (ttn : TTName) -> Eff TTName [STATE CTX]
  addEnv q ttn = do
    id  <- freshId
    ctx <- get
    let ttn' = case lookupBy ttnEq ttn (env ctx) of
                 Just _  => UN $ show ttn ++ "_" ++ show id
                 Nothing => ttn
    put $ record { env = (ttn', MkQ q) :: (env ctx) } ctx
    pure ttn'

  updateTTName : (ttn' : TTName) ->
                 Guard cs cs' ((u,ttn,ppp) :: bctx)
                       (Query a ((u,ttn,ppp) :: bctx)) ->
                 Guard cs cs' ((u,ttn',ppp) :: bctx)
                       (Query a ((u,ttn',ppp) :: bctx))
  updateTTName _ = really_believe_me

  setPiProcs : Place -> (PiProc -> PiProc) -> Eff () [STATE CTX]
  setPiProcs AtAlice pi = do
    ctx <- get
    let pips  = piprocs ctx
    let pips' = record { alicePi = \k => (alicePi pips) $ pi k } pips
    put $ record { piprocs = pips' } ctx
  setPiProcs AtApp pi = do
    ctx <- get
    let pips  = piprocs ctx
    let pips' = record { appPi = \k => (appPi pips) $ pi k } pips
    put $ record { piprocs = pips' } ctx
  setPiProcs AtDB pi = do
    ctx <- get
    let pips  = piprocs ctx
    let pips' = record { dbPi = \k => (dbPi pips) $ pi k } pips
    put $ record { piprocs = pips' } ctx
  setPiProcs (AtFrag fId) pi = do
    ctx <- get
    let pips  = piprocs ctx
    let pips' = record { fragsPi =
      let frags  = fragsPi pips
          fragPi = case lookup (AtFrag fId) frags of
                     Just fPi => \k => fPi $ pi k
                     Nothing  => pi
      in update ((AtFrag fId), fragPi) frags } pips
    put $ record { piprocs = pips' } ctx

  -- See if `q'` involves some variable. If yes, it means that DB
  -- requires data from App. So, take a look at the piproc of DB. If
  -- there is no receiving of the data, then add it.
  -- DB.
  piProcsForQ : (q : Query u bctx) -> (qvar : Query u bctx) ->
                Process -> Eff () [STATE CTX]
  piProcsForQ q qvar (rc,cr,ce) = do
    -- Caller
    setPiProcs cr (PiSend (MkPiChan ce) (MkPiChan rc) (MkPiVal qvar))
    -- Callee
    setPiProcs ce (PiGet (MkPiChan ce) (MkPiVal q))
    setPiProcs ce (PiSend (MkPiChan rc) (MkPiChan rc) (MkPiVal qvar))
    -- Recipient
    setPiProcs rc (PiGet (MkPiChan rc) (MkPiVal qvar))

  genPi' : Guard cs cs' bctx (Query u bctx) -> Eff (Query u bctx) [STATE CTX]
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
    -- Get the query with a default val.
    let q' = q (defaultQVal (SCH s) (AtApp, AtApp, AtDB) bctx)
    -- At this time, we don't know the `Recipient` of the query. The
    -- recipient will be know at `Bind` time. So we defer the process
    -- of `q'` until the `Bind`.
    ctx <- get
    put $ record { callee = Just AtDB } ctx
    pure q'
  genPi' (QueryF fId q {ss}) {bctx} = do
    -- 1. parse q'. If it involve sending to Frag. Look at DB if the
    -- sending is already done or done it.
    ctx <- get
    let s = getSchema fId ss
    let q' = q (defaultQVal (SCH s) (AtApp, AtApp, AtFrag fId) bctx)
    put $ record { callee = Just (AtFrag fId) } ctx
    pure q'
  genPi' (Let ttn q g)              = do
      -- FIXME: if `e` involve Alice Data, the let should be done at
      -- Alice place, And Alice should send the result. Actually, I made
      -- the assumption that it is done at App place.
      ttn' <- addEnv q ttn
      let g' = updateTTName ttn' g
      innerQ <- genPi' g'
      pure $ downQ innerQ
    where
    -- Si l'innerQ est une QVar et que c'est stop, je dois en faire
    -- une QVar_. Si c'est Pop, je dépile. Si c'est autre chose, je
    -- laisse allé.
    downQ : Query u (z :: bctx) -> Query u bctx
    downQ (QVar Stop) {z=(u,ttn,ppp)} {bctx} = QVar_ ttn u ppp {bctx}
    downQ (QVar (Pop prf)) {bctx}            = QVar prf {bctx}
    downQ q                                  = really_believe_me q
  genPi' (Pure x) = pure x
  genPi' (SeqApp Privy g)           = do
    e <- genPi' g
    pure (QPrivy e)
  genPi' (Bind g f)                 = do
      -- J'ajoute q dans le context, puis j'en fais une var.
      q   <- genPi' g
      ttn <- addEnv q (UN "var")
      ctx <- get
      let qvar = QVar_ ttn (getU q) (getProcess q)
      case callee ctx of
        Just ce => do
          let rc = recipient (getProcess q)
          let cr    = AtApp
          -- Je construit le piproc
          piProcsForQ q qvar (rc,cr,ce)
        Nothing => pure ()
      genPi' (f qvar)
      -- id  <- freshId
      -- ctx <- get
      -- let ttn = UN $ "var_" ++ show id
      -- let qvar = QVar_ ttn (getU q) (getProcess q)
      -- -- Add new variable into the context
      -- put $ record { env = updateBy ttnEq (ttn, MkQ q) (env ctx) } ctx
      -- -- FIXME: Ici, c'est forcement une query retourné par un Query
      -- -- ou en let. Si, c'est par un let, la QVar_ existe déjà! ça ne
      -- -- sert a rien de l'ajouter.
      -- genPi' (f qvar)



  genPi : Guard (Plain s) cs' [] (Query u []) -> IO ()
  genPi g {s} {u} {cs'} =
      let keys_    = the (List ((String, U), String)) []
          callee_  = the (Maybe Place) Nothing
          env_     = the (List (TTName, Q)) []
          piprocs_ = initPiProcs cs'
          id_      = 0
      in runInit [(MkCTX keys_ callee_ env_ piprocs_ id_), ()] $ do
            q   <- genPi' g
            ctx <- get
            -- Now update piprocs (from ctx) with q and update it
            let piprocs_ = CTX.piprocs ctx
            putStr $ show piprocs_
    where
    genAtFrag : (m : Nat) -> (n : Nat) -> List Place -> List Place
    genAtFrag Z     n ps = case natToFin Z n of
                              Just fId => AtFrag fId :: ps
                              Nothing  => ps
    genAtFrag (S k) n ps = case natToFin (S k) n of
                              Just fId => AtFrag fId :: (genAtFrag k n ps)
                              Nothing  => genAtFrag k n ps

    initPiProcs : CState -> PiProcs
    initPiProcs (Plain  _)     =
      MkPiProcs id id id Nil
    initPiProcs (FragV ss {n}) =
      let fPlaces  = genAtFrag n n []
          fPiProcs = replicate n id
          fragsPi   = the (List (Place, (PiProc -> PiProc))) $
                     zip fPlaces fPiProcs
      in MkPiProcs id id id fragsPi

  -- lala : Guard (Plain s) cs' [] (Query a []) -> IO ()
  -- lala g = genPi g

main : IO ()
main = genPi (do placesF_2Let
                 placesF_3Let
                 meetingFDo' (encrypt "mykey" "toto"))

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
