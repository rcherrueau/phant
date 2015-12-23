module phant.crypt

%default total


Key : Type
Key = String

-- Symmetric encryption
namespace sym

  class Crypt a b where
    encrypt : Key -> a -> b
    decrypt : Key -> b -> Maybe a

  -- AES
  -- abstract data AES a = MkAES Key a
  abstract data AES : (a : Type) -> Type where
    MkAES : Key -> (v : a) -> AES a

  instance Crypt a (AES a) where
    encrypt k  s            = MkAES k s
    decrypt k1 (MkAES k2 y) = case k1 == k2 of
                                   True  => Just y
                                   False => Nothing

  instance Eq a => Eq (AES a) where
    (MkAES k1 x) == (MkAES k2 y) = k1 == k2 && x == y

-- namespace asym
