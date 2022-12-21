{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverlappingInstances #-}

module Background where

-- Symbolic Expressions

data Expr v  =  Var v |  Zero |  One
             |  Plus (Expr v) (Expr v) |  Times  (Expr v) (Expr v)

instance Show a => Show (Expr a) where
  showsPrec p (Var x)  =  showsPrec p x
  showsPrec p Zero     =  shows 0
  showsPrec p One      =  shows 1
  showsPrec p (Plus e1 e2)   =  showParen (p >= 6) $ (showsPrec 6 e1) . (" + " ++) . (showsPrec 6 e2)
  showsPrec p (Times e1 e2)  =  showParen (p >= 7) $ (showsPrec 7 e1) . (" * " ++) . (showsPrec 7 e2)

data X = X deriving (Show, Eq, Ord)

example1 :: Expr X
example1 = Times (Var X) (Plus (Var X) One)

-- Semirings

class Monoid d => Semiring d where
   zero   :: d
   one    :: d
   plus   :: d -> d -> d
   times  :: d -> d -> d

infixl 6 `plus`
infixl 7 `times`

instance Num a => Semigroup a where
   (<>) = (+)

instance Num a => Monoid a where
   mempty = 0

instance Num a => Semiring a where
   zero   = 0
   one    = 1
   plus   = (+)
   times  = (*)

instance Semigroup (Expr v) where
   (<>) = plus

instance Monoid (Expr v) where
   mempty = zero

instance Semiring (Expr v) where
   zero   = Zero
   one    = One
   plus   = Plus
   times  = Times

-- Evaluation

eval :: Semiring d => (v -> d) -> Expr v -> d
eval var (Var x)         =  var x
eval var Zero            =  zero
eval var One             =  one
eval var (Plus   e1 e2)  =  eval var e1  `plus`   eval var e2
eval var (Times  e1 e2)  =  eval var e1  `times`  eval var e2

test1 :: Int
test1 = eval (\X -> 5) example1
-- 30

-- Symbolic Differentiation

deriv :: Eq v => v -> Expr v -> Expr v
deriv x (Var y)         =  if x == y then One else Zero
deriv x Zero            =  Zero
deriv x One             =  Zero
deriv x (Plus   e1 e2)  =  Plus (deriv x e1) (deriv x e2)
deriv x (Times  e1 e2)  =  Plus (Times e2 (deriv x e1)) (Times e1 (deriv x e2))

deriv' :: Eq v => v -> Expr v -> (Expr v, Expr v)
deriv' x (Var y)         =  (Var y,  if x == y then one else zero)
deriv' x Zero            =  (zero,   zero)
deriv' x One             =  (one,    zero)
deriv' x (Plus   e1 e2)  =  let  (e1', de1)  =  deriv' x e1
                                 (e2', de2)  =  deriv' x e2
                            in   (e1' `plus` e2', de1 `plus` de2)
deriv' x (Times  e1 e2)  =  let  (e1', de1)  =  deriv' x e1
                                 (e2', de2)  =  deriv' x e2
                            in   (e1 `times` e2', (e2' `times` de1) `plus` (e1' `times` de2))

symbolic :: Eq v => v -> Expr v -> Dual (Expr v)
symbolic x  = eval gen where  gen y  = D (Var y) (ddx y)
                              ddx y  = if x == y then one else zero

-- Dual numbers

data Dual d = D { fstD :: d, sndD :: d }  deriving (Show, Functor)

instance Semiring d => Semigroup (Dual d) where
   (<>) = plus

instance Semiring d => Monoid (Dual d) where
   mempty = zero

instance Semiring d => Semiring (Dual d) where
   zero                         = D  zero           zero
   one                          = D  one            zero
   (D f df)  `plus`   (D g dg)  = D  (f `plus`  g)  (df `plus` dg)
   (D f df)  `times`  (D g dg)  = D  (f `times` g)  ((g `times` df) `plus` (f `times` dg))

-- Classic Forward-mode Automatic Differentiation

forwardAD :: (Eq v, Semiring d) => (v -> d) -> v -> Expr v -> Dual d
forwardAD var x = eval gen where  gen y  = D (var y) (ddx y)
                                  ddx y  = if x == y then one else zero

test2 :: Dual Int
test2 = forwardAD (\X -> 5) X example1
-- D {fstD = 30, sndD = 11}
