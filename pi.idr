module phant.pi

import ra

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

-- x : PiVal
-- x = MkPiVal "x"

-- y : PiVal
-- y = MkPiVal "y"

-- z : PiVal
-- z = MkPiVal "z"

-- pi1 : PiProc
-- pi1 = PiMkChan x (PiPar (PiSend x y PiEnd)
--                         (PiGet x y (PiSend y x (PiGet x y PiEnd))))


-- piget_cps : PiVal -> PiVal -> PiProc -> ((PiProc -> r) -> r)
-- piget_cps x y z = \k => k (PiGet x y z)

-- pisend_cps : PiVal -> PiVal -> PiProc -> ((PiProc -> r) -> r)
-- pisend_cps x y z = \k => k (PiSend x y z)


-- pipar_cps : PiProc -> PiProc -> ((PiProc -> r) -> r)
-- pipar_cps x y = \k => k (PiPar x y)

-- piend_cps : ((PiProc -> r) -> r)
-- piend_cps = \k => k PiEnd

-- pichan_cps : PiVal -> PiProc -> ((PiProc -> r) -> r)
-- pichan_cps x y = \k => k (PiMkChan x y)
