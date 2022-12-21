{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}

module ForwardMode where

import Background
import AbstractAD

import Data.Map

-- Forward-Mode AD as AD in the Dense Function Space

newtype Dense v d = Dense { dense :: v -> d } deriving Functor

instance Semigroup e => Semigroup (Dense v e) where
  f <> g = Dense (\ v -> dense f v <> dense g v)

instance Monoid d => Monoid (Dense v d) where
  mempty = Dense (\ v -> mempty)

instance Semiring d => Semiring (Dense v d) where
  zero = Dense $ \ _ -> zero
  one  = Dense $ \ _ -> one
  f `plus` g = Dense $ \ v -> dense f v `plus` dense g v
  f `times` g = Dense $ \ v -> dense f v `times` dense g v

instance Semiring d => SModule d (Dense v d) where
  d `sact` f   = Dense (\ v -> d `times` (dense f v))

instance (Eq v, Semiring d) => Kronecker v d (Dense v d) where
  delta v  = Dense (\ w -> if v == w then one else zero)

forwardADDense :: Kronecker v d e => (v -> d) -> Expr v -> Nagata d e
forwardADDense = abstractAD

data XX = X1 | X2 deriving (Eq, Ord, Show)

example2 :: Expr XX
example2 = Plus (Plus (Times (Var X1) (Var X2)) (Var X1)) One

test3 :: (Int, Int)
test3 = let {var X1 = 5; var X2 = 3; e = dense (tanN (forwardADDense var example2))}
        in  (e X1, e X2)
-- (4,5)

-- Correct AD Variants by Construction

class Kronecker v d e => CorrectAD v d e where
   rep  :: Dense v d -> e
   abs  :: e -> Dense v d

-- Sparse Maps

newtype Sparse v d = Sparse { sparse :: Map v d } deriving (Show)

abs_ :: (Ord v, Semiring d) => Sparse v d -> Dense v d
abs_ m = Dense (\ v -> findWithDefault zero v (sparse m))

rep_ :: (Bounded v, Semiring d, Ord v, Eq d, Enum v) => Dense v d -> Sparse v d
rep_ f = Sparse (fromList [ (v, dense f v) | v <- [minBound..maxBound], dense f v /= zero])

instance (Ord v, Semiring d) => Semigroup (Sparse v d) where
  (Sparse f) <> (Sparse g) = Sparse $ unionWith plus f g

instance (Ord v, Semiring d) => Monoid (Sparse v d) where
  mempty = Sparse empty

instance (Ord v, Semiring d) => SModule d (Sparse v d) where
  d `sact` (Sparse m) = Sparse $ fmap (d `times`) m

instance (Ord v, Semiring d) => Kronecker v d (Sparse v d) where
  delta v = Sparse $ singleton v one

instance (Ord v, Bounded v, Enum v, Semiring d, Eq d)
  => CorrectAD v d (Sparse v d) where
    rep  = rep_
    abs  = abs_

forwardADSparse :: (Ord v, Semiring d) => (v -> d) -> Expr v -> Nagata d ((Sparse v d))
forwardADSparse = abstractAD

test4 :: Map XX Int
test4 = let {var X1 = 5; var X2 = 3} in sparse $ tanN (forwardADSparse var example2)
-- fromList [(X1,4),(X2,5)]
