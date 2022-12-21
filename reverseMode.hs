{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TypeOperators #-}

module ReverseMode where

import Background
import AbstractAD
import ForwardMode

import Data.Map
import Prelude hiding (abs)
import Data.Array.Base (MArray(..))
import Control.Monad.Reader
import Control.Monad.ST
import Data.Array.ST

-- Accumulating Multiplications

newtype PW d e = PW { unPW :: d -> e }

repPW :: SModule d e => e -> PW d e
repPW e = PW (\d -> d `sact` e)

absPW :: SModule d e => PW d e -> e
absPW f = unPW f one

instance Semigroup e => Semigroup (PW d e) where
  PW f <> PW g = PW (\d -> f d <> g d)

instance Monoid e => Monoid (PW d e) where
  mempty               = PW (\d -> mempty)
  PW f `mappend` PW g  = PW (\d -> f d `mappend` g d)

instance SModule d e => SModule d (PW d e) where
  d' `sact` (PW f) = PW (\d -> f (d' `times` d))

instance Kronecker v d e => Kronecker v d (PW d e) where
  delta v = PW (\d -> d `sact` delta v)

instance (Ord v, Semiring d) => Kronecker v d (PW d (Sparse v d)) where
    delta v = PW (\d -> Sparse $ singleton v d)

instance CorrectAD v d e => CorrectAD v d (d `PW` e) where
    rep  = repPW . rep
    abs  = abs . absPW

reverseAD :: (Ord v, Semiring d) => (v -> d) -> Expr v -> Nagata d (PW d (Sparse v d)) -- Nagata d (d -> Map v d)
reverseAD = abstractAD

example3 :: Expr X
example3 = Times (Var X) (Times (Plus (Var X) One) (Plus (Var X) (Var X)))

test5 :: Map X Int
test5 = (sparse . absPW . tanN) (reverseAD (\X -> 5) example3)
-- fromList [(X,170)]

-- Accumulating Additions

newtype Cayley e = C { unC :: e -> e }

reprC :: Monoid e => e -> Cayley e
reprC e = C (\e' -> e' <> e)

absC :: Monoid e => Cayley e -> e
absC f = unC f mempty

instance Semigroup (Cayley e) where
  C f <> C g = C (g . f)

instance Monoid (Cayley e) where
  mempty = C id
  C f `mappend` C g = C (g . f)

instance SModule d e => SModule d (Cayley e) where
  d `sact` f = reprC (d `sact` absC f)

instance Kronecker v d e => Kronecker v d (Cayley e) where
  delta v =  C (\ e -> e <> delta v)

instance (Ord v, Semiring d) => Kronecker v d (PW d (Cayley (Sparse v d))) where
  delta v = PW (\d -> C (\e -> Sparse (insertWith plus v d (sparse e))))

instance CorrectAD v d e => CorrectAD v d (Cayley e) where
   rep = reprC . rep
   abs = abs . absC

reverseAD_Cayley :: (Ord v, Semiring d) => (v -> d) -> Expr v -> Nagata d (PW d (Cayley (Sparse v d)))
reverseAD_Cayley = abstractAD

test6 :: Map X Int
test6 = (sparse . absC . absPW . tanN) (reverseAD_Cayley (\X -> 5) example3)
-- fromList [(X,170)]

-- Array-based Reverse Mode

newtype STCayley v d = STC { unSTC :: forall s. ReaderT (STArray s v d) (ST s) () }


repST :: (Ix v, Semiring d) => Cayley (Sparse v d) -> STCayley v d
repST m = foldMap (\(v,d) -> modifyAt (\ d' -> d' `plus` d) v) (toList (sparse (unC m (Sparse empty))))

absST :: (Ix v, Semiring d, Bounded v) => STCayley v d -> Cayley (Sparse v d)
absST p = C $ runST $
   do  arr <- newArray (minBound,maxBound) zero
       runReaderT (unSTC p) arr
       l <- getAssocs arr
       return $ Sparse . foldMap (\ (k,v) -> insertWith plus k v) l . sparse

modifyAt :: Ix v => (d -> d) -> v -> STCayley v d
modifyAt f v = STC (do arr <- ask; a <- readArray arr v ; writeArray arr v (f a))

instance MArray arr e m => MArray arr e (ReaderT x m) where
  getBounds = lift . getBounds
  getNumElements = lift . getNumElements
  unsafeRead arr i = lift (unsafeRead arr i)
  unsafeWrite arr i v = lift (unsafeWrite arr i v)

instance Semigroup (STCayley v d) where
  (STC com) <> (STC com') = STC (com >> com')

instance Monoid (STCayley v d) where
  mempty = STC $ return ()

instance (Semiring d) => SModule d (STCayley v d) where
  d `sact` e = undefined -- unused when Mutant is combined with |PW| and awkward to define

instance (Ix v, Semiring d, Bounded v) => Kronecker v d (d `PW` STCayley v d) where
  delta v = PW $ \d -> modifyAt (`plus` d) v

instance (Ix v, Bounded v, Semiring d) => Kronecker v d (STCayley v d) where
  delta v = modifyAt (plus one) v

instance (Ix v, Ord v, Bounded v, Enum v, Semiring d, Eq d) => CorrectAD v d (STCayley v d)  where
  rep = repST . rep
  abs = abs   . absST

reverseAD_M  :: (Ix v, Semiring d, Bounded v) => (v -> d) -> Expr v -> Nagata d (d `PW` STCayley v d)
reverseAD_M = abstractAD

instance Ix X where
   range (X, X) = [X]
   inRange (X, X) X = True
   index (X, X) X = 0

instance Bounded X where
  minBound = X
  maxBound = X

test7 :: Map X Int
test7 = (sparse . absC . absST . absPW . tanN) (reverseAD_M (\X -> 5) example3)
-- fromList [(X,170)]
