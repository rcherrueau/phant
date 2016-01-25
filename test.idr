module phant.test

import crypt
import guard

D : Attribute
D = ("Date", NAT)

N : Attribute
N = ("Name", TEXT)

A : Attribute
A = ("Addr", TEXT)

C_ : Attribute -> Attribute
C_ (n, u) = (n, CRYPT u)

-- nextWeek : Expr (getU D) p -> Expr BOOL AppP
-- nextWeek _ = ExprBOOL True
nextWeek : {bctx : Vect n Ctx} -> {bctx' : Vect m Ctx} -> Query NAT bctx -> Query BOOL bctx'
nextWeek _ = QVal True

-- -- 1
-- places : Guard (Plain [D,N,A]) (Plain [D,N,A]) Nil (Expr (SCH [A]) Nil)
placesDB : GUARD (DB[D,N,A]) -> (SCH [A])
placesDB = guard(
  Query (QProject [A] . (QSelect D nextWeek)))


-- -- 2
-- meetings : Guard (Plain [D,N,A]) (Plain [D,N,A]) Nil (Expr (SCH [D,Count]) Nil)
meetingsDB : GUARD (DB[D,N,A]) -> (SCH [D,Count])
meetingsDB = guard(
  Query (QCount [D] . QSelect N (QEq (QVal "Bob" {bctx=[]}))))


-- -- 1 & 2
-- compose : Guard (Plain [D,N,A]) (Plain [D,N,A]) (Expr (SCH [A,D,Count]) Nil)
composeDB : GUARD (DB[D,N,A]) -> (SCH [A,D,Count])
composeDB = guard(
  placesDB               >>= \q1 =>
  meetingsDB             >>= \q2 =>
  Pure (QProduct q1 q2))

-- composeDo : Guard (Plain [D,N,A]) (Plain [D,N,A]) (Expr (SCH [A,D,Count]) Nil)
composeDB' : GUARD (DB[D,N,A]) -> (SCH [A,D,Count])
composeDB' = guard(do
  q1 <- placesDB
  q2 <- meetingsDB
  pure (QProduct q1 q2))


-- -- -- left-first strategy
-- -- -- 3
-- -- placesF : Guard (Plain [D,N,A]) (FragV [[D,Id], [C_ N,A,Id]]) (Expr (SCH [A]) Nil)
-- placesF : GUARD (DB[D,N,A]) ~> (FRAG[[D,Id], [C_ N,A,Id]]) -> (SCH [A])
-- placesF = guard(
--   Encrypt "mykey" N                                      >>= \_ =>
--   Frag [[D]]                                             >>= \_ =>
--   QueryF 0 (QProject [Id] . QSelect D nextWeek)          >>= \ids =>
--   QueryF 1 (QProject [A] . QSelect Id (flip QElem ids))  >>= \res =>
--   Pure res)

-- placesFDo : Guard (Plain [D,N,A]) (FragV [[D,Id], [C_ N,A,Id]]) (Expr (SCH [A]) Nil)
placesFDo : GUARD (DB[D,N,A]) ~> (FRAG[[D,Id], [C_ N,A,Id]]) -> (SCH [A])
placesFDo = guard(do
  Encrypt "mykey" N
  Frag [[D]]
  ids <- QueryF 0 (QProject [Id] . QSelect D nextWeek)
  res <- QueryF 1 (QProject [A] . QSelect Id (flip QElem ids))
  pure res)


-- -- 4
-- placesF_2 : Guard (Plain [D,N,A]) (FragV [[D,Id], [C_ N,A,Id]]) (Expr (SCH [A]) Nil)
placesF_2 : GUARD (DB[D,N,A]) ~> (FRAG[[D,Id], [C_ N,A,Id]]) -> (SCH [D,A])
placesF_2 = guard(
  Encrypt "mykey" N                                               >>= \_ =>
  Frag [[D]]                                                      >>= \_ =>
  QueryF 0 (QProject [D, Id] . QSelect D nextWeek)                >>= \dIds =>
  Let (UN "ids") (QProject [Id] dIds) (
    QueryF 1 (QProject [A] . QSelect Id (flip QElem (var_ Stop))) >>= \res =>
    Pure (QProject [D,A] $ QProduct dIds res)))

-- placesF_2DO : Guard (Plain [D,N,A])(FragV [[D,Id], [C_ N,A,Id]]) (Expr (SCH [A]) Nil)
placesF_2Do : GUARD (DB[D,N,A]) ~> (FRAG[[D,Id], [C_ N,A,Id]]) -> (SCH [D,A])
placesF_2Do = guard(do
  Encrypt "mykey" N
  Frag [[D]]
  dIds <- QueryF 0 (QProject [D, Id] . QSelect D nextWeek)
  Let (UN "ids") (QProject [Id] dIds) (do
    res <- QueryF 1 (QProject [A] . QSelect Id (flip QElem (var_ Stop)))
    pure (QProject [D,A] $ QProduct dIds res)))

-- placesFDo'' : Guard (Plain [D,N,A]) (FragV [[D,Id], [Nc,A,Id]]) Nil (Expr (SCH [D,A]))
placesF_2Let : GUARD (DB[D,N,A]) ~> (FRAG[[D,Id], [C_ N,A,Id]]) -> (SCH [D,A])
placesF_2Let =  guard(do
  Encrypt "mykey" N
  Frag [[D]]
  dIds <- QueryF 0 (QProject [D, Id] . QSelect D nextWeek)
  let truc = dIds
  let ids = QProject [Id] dIds
  res <- QueryF 1 (QProject [A] . QSelect Id (flip QElem ids))
  pure (QProject [D,A] $ QProduct dIds res))

placesF_3Let : GUARD (DB[D,N,A]) ~> (FRAG[[D,Id], [C_ N,A,Id]]) -> (UNIT)
placesF_3Let =  guard(do
  Encrypt "mykey" N
  Frag [[D]]
  dIds <- QueryF 0 (QProject [D, Id] . QSelect D nextWeek)
  let ids = QProject [Id] dIds
  ql <- QueryF 1 (QProject [A] . QSelect Id (flip QElem ids))
  let res = QProject [D,A] $ QProduct ids ql
  pure $ QVal ())

-- -- -- 5
-- meetingF : AES String -> GUARD (FRAG[[D,Id], [C_ N,A,Id]]) -> (SCH [D,Id])
-- meetingF c = guard(
--   QueryF 0 (QProject [D, Id])                          >>= \ql =>
--   QueryF 1 (QProject [Id] .
--             QSelect (C_ N) (QEq (QVal c {bctx=[]})))   >>= \qr =>
--   Pure (QProduct ql qr))

-- meetingFDo : AES String -> GUARD (FRAG[[D,Id], [C_ N,A,Id]]) -> (SCH [D,Id])
-- meetingFDo c = guard(do
--   ql <- QueryF 0 (QProject [D, Id])
--   qr <- QueryF 1 (QProject [Id] . QSelect (C_ N) (QEq (QVal c {bctx=[]})))
--   pure (QProduct ql qr))


-- -- -- 6
-- meetingF' : AES String -> GUARD (FRAG[[D,Id], [C_ N,A,Id]]) -> (SCH [D,A])
-- meetingF' c = guard(
--   Privy <*> QueryF 0 (QProject [D, Id])                         >>= \ql =>
--   Privy <*> QueryF 1 (QProject [A, Id] .
--                       QSelect (C_ N) (QEq (QVal c {bctx=[]})))  >>= \qr =>
--   Pure (QProject [D,A] $ QProduct ql qr))

-- meetingFDo' : AES String -> GUARD (FRAG[[D,Id], [C_ N,A,Id]]) -> (SCH [D,A])
-- meetingFDo' c = guard(do
--   ql <- Privy <*> QueryF 0 (QProject [D, Id])
--   qr <- Privy <*> QueryF 1 (QProject [A, Id] .
--                             QSelect (C_ N) (QEq (QVal c {bctx=[]})))
--   pure (QProject [D,A] $ QProduct ql qr))
