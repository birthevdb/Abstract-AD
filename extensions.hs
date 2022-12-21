{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Extensions where

import Background
import AbstractAD
import ForwardMode
import ReverseMode

import Data.Map
import Prelude hiding (abs,lookup,sin,cos)

-- Additional Primitives

class Semiring d => Ring d where
  neg :: d -> d

class Ring d => Trig d where
  sin :: d -> d
  cos :: d -> d

instance (SModule d e, Ring d, Ring e) => Ring (Nagata d e) where
  neg (N d df) = N (neg d) (neg df)

instance (SModule d e, Trig d, Trig e) => Trig (Nagata d e) where
  sin (N f df) = N (sin f) (cos f `sact` df)
  cos (N f df) = N (cos f) (neg (sin f `sact` df))

-- Overloading Initial Expressions

example2' :: Semiring d => d -> d -> d
example2' x y = ((x `times` y) `plus` x) `plus` one

test8 :: Nagata Int (Sparse XX Int)
test8 = example2' (N 5 (delta X1)) (N 3 (delta X2))
-- N {priN = 21, tanN = Sparse {sparse = fromList [(X1,4),(X2,5)]}}

test9 :: Expr XX
test9 = example2' (Var X1) (Var X2)

-- Higher-order derivatives

derive2nd :: (Eq v, Semiring d) => (v -> d) -> Expr v -> Dense v (Dense v d)
derive2nd var = fmap (fmap (eval var) . tanN . forwardADDense Var) . tanN . forwardADDense Var

derive2nd' :: forall v d . (Eq v, Semiring d) => (v -> d) -> v -> v -> Expr v -> d
derive2nd' var x y e = dense (tanN (dense (tanN ((forwardADDense gen e) :: Nagata (Nagata d (Dense v d)) (Dense v (Nagata d (Dense v d))))) x)) y
    where gen z = N (var z) (delta z)

-- Compact version

data N2nd v d = N2nd d (Dense v (Nagata d (Dense v d)))

d2N (N2nd x y)  =  x
e2N (N2nd x y)  =  y

instance Semiring d => Semigroup (N2nd v d) where
  (<>) = plus

instance Semiring d => Monoid (N2nd v d) where
  mempty = zero

instance (Semiring d) => Semiring (N2nd v d) where
  zero        =  N2nd zero zero
  one         =  N2nd one  zero
  N2nd x f `plus`  N2nd y g   =  N2nd (x `plus` y)   (f `plus` g)
  N2nd x f `times` N2nd y g   =  N2nd (x `times` y)  (Dense $ \ v ->
            let  N df ddf = dense f v
                 N dg ddg = dense g v
            in   N ((x `times` dg ) `plus` (y `times` df))
                  (Dense $ \ w -> (x `times` dense ddg w) `plus`
                                  (y `times` dense ddf w) `plus`
                                  (df `times` dg) `plus`
                                  (dg `times` df)))

forward2nd :: (Semiring d, Eq v) => (v -> d) -> Expr v -> N2nd v d
forward2nd var = eval gen where gen x = N2nd (var x) (delta x)

instance Show d => Show (Dense X d) where
  show f = "(\\ X -> " ++ show (dense f X) ++ ")"

deriving instance Show d => Show (N2nd X d)

test10 :: N2nd X Int
test10 = forward2nd (\ X -> 5) example3
-- N2nd 300 (\ X -> N {priN = 170, tanN = (\ X -> 64)})

-- Higher-order Derivatives with Streams

data Stream v d = d :< Dense v (Stream v d)
deriving instance Show d => Show (Stream X d)
infixr 5 :<

instance Semiring d => Semigroup (Stream v d) where
  (<>) = plus

instance Semiring d => Monoid (Stream v d) where
  mempty = zero

instance Semiring d => Semiring (Stream v d) where
  zero  = zero :< zero
  one   = one :< zero
  (x :< xs)     `plus`  (y :< ys)      = (x `plus` y)  :< (xs `plus` ys)
  xxs@(x :< xs) `times` yys@(y :< ys)  = (x `times` y) :< Dense (\ v -> ((dense xs v `times` yys)
                                                          `plus` (xxs  `times` dense ys v)))

forwardAll :: (Eq v, Semiring d) => (v -> d) -> Expr v -> Stream v d
forwardAll var  =  eval gen where
                   gen y = var y :< delta y

test11 :: Stream X Int
test11 = forwardAll (\X -> 5) example3
-- 300 :< (\ X -> 170 :< (\ X -> 64 :< (\ X -> 12 :< (\ X -> 0 :< ....

-- Basic Sharing of Subexpressions

data  ExprT v   =  TVar v |  TZero |  TOne |  TPlus   (ExprT v) (ExprT v)
                |  TTimes  (ExprT v) (ExprT v) |  TLet v (ExprT v) (ExprT v)

teval :: (Eq v, Semiring d) => (v -> d) -> ExprT v -> d
teval gen (TVar v)            =  gen v
teval gen TZero               =  zero
teval gen TOne                =  one
teval gen (TPlus   se1  se2)  =  teval gen se1  `plus`   teval gen se2
teval gen (TTimes  se1  se2)  =  teval gen se1  `times`  teval gen se2
teval gen (TLet y  se1  se2)  =  let  d1  =  teval gen se1
                                      gen2  = \ x -> if x == y then d1 else gen x
                                 in   teval gen2 se2

abstractADT :: (Eq v, Letin v d e) => (v -> d) -> ExprT v -> Nagata d e
abstractADT var = teval gen where gen x = N (var x) (delta x)

class CorrectAD v d e => Letin v d e where
  letin :: v -> e -> e -> e
  letin y de1 de2 = ((dense (abs de2) y) `sact` de1) <> de2

teval' :: (Eq v, Letin v d e) => (v -> Nagata d e) -> ExprT v -> Nagata d e
teval' gen (TVar v)            =  gen v
teval' gen TZero               =  zero
teval' gen TOne                =  one
teval' gen (TPlus   se1  se2)  =  teval gen se1  `plus`   teval gen se2
teval' gen (TTimes  se1  se2)  =  teval gen se1  `times`  teval gen se2
teval' gen (TLet y  se1  se2)  =   let  N f1 df1  =  teval' gen se1
                                        gen2       =  \ x -> if x == y then N f1 (delta y) else gen x
                                        N f2 df2  =  teval' gen2 se2
                                   in   N f2 (letin y df1 df2)

instance (Ord v, Bounded v, Enum v, Eq d, Semiring d) => Letin v d (Hom d (Cayley (Sparse v d))) where
  letin y de1 de2
   = H (\ n -> (C (\ m -> let  m' = unC (unH de2 n) m
                           in   unC (unH de1 (sparse m' ! y)) m')))

letin2 y de1 de2
  = H (\ n -> (C (\ m -> let  old = lookup y (sparse m)
                              m'  = unC (unH de2 n) m
                         in   unC (unH de1 (sparse m' ! y)) (Sparse (update (const old) y (sparse m'))))))
