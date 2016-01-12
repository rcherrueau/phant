module phant.pi

data PiVal : Type where
  MkPiVal : a -> PiVal

data PiProc : Type where
  PiGet :    PiVal -> PiVal -> PiProc -> PiProc
  PiSend :   PiVal -> PiVal -> PiProc -> PiProc
  PiPar :    PiProc -> PiProc -> PiProc
  PiMkChan : PiVal -> PiProc -> PiProc
  PiBang :   PiProc -> PiProc
  PiEnd :    PiProc

x : PiVal
x = MkPiVal "x"

y : PiVal
y = MkPiVal "y"

z : PiVal
z = MkPiVal "z"

pi1 : PiProc
pi1 = PiMkChan x (PiPar (PiSend x y PiEnd)
                        (PiGet x y (PiSend y x (PiGet x y PiEnd))))
