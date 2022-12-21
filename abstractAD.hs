{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

module AbstractAD where

import Background

-- Modules over Semirings

class (Semiring d, Monoid e) => SModule d e | e -> d where
    sact :: d -> e -> e
infixl 7 `sact`

-- Nagata Numbers

data Nagata d e = N {  priN  :: d, tanN  :: e  } deriving (Show)

instance Functor (Nagata d) where
   fmap h (N f df) = N f (h df)

-- Theorem: Given a d-module e, then Nagata d e admits a semiring structure.

instance SModule d e => Semigroup (Nagata d e) where
  (<>) = plus

instance SModule d e => Monoid (Nagata d e) where
  mempty = zero
  mappend = plus

instance SModule d e => SModule d (Nagata d e) where
  d' `sact` (N d e) = N (d' `times` d) (d' `sact` e)

instance SModule d e => Semiring (Nagata d e) where
  zero                         = N  zero           mempty
  one                          = N  one            mempty
  (N f df) `plus`  (N g dg)  = N  (f `plus`  g)  (df `mappend` dg)
  (N f df) `times` (N g dg)  = N  (f `times` g)  ((f `sact` dg) `mappend` (g `sact` df))

-- Kronecker Delta

class SModule d e => Kronecker v d e where
  delta :: v -> e

-- Abstract Automatic Differentiation

abstractAD :: Kronecker v d e => (v -> d) -> Expr v -> Nagata d e
abstractAD var = eval gen where gen x = N (var x) (delta x)
