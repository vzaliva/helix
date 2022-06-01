#!/usr/bin/env stack
{- stack
  runghc
  --package QuickCheck
  --package fp-ieee
  --package floating-bits
-}

{-# LANGUAGE DeriveFunctor   #-}
{-# LANGUAGE Rank2Types      #-}
{-# LANGUAGE TemplateHaskell #-}

import           Control.Monad

import           GHC.Float               (double2Float, float2Double)

import           Data.Functor
import           Data.List
import           Data.Ratio

import           Text.Printf

-- QickCheck
import           Test.QuickCheck

-- floating-bits
import           Data.Bits.Floating
import           Data.Bits.Floating.Prim (double2WordBitwise, float2WordBitwise)
import           Data.Bits.Floating.Ulp

-- fp-ieee
import qualified Numeric.Floating.IEEE   as IEEE

--------------------------------------------------------------------------------
-- | = aux
--------------------------------------------------------------------------------

type Binary32 = Float
type Binary64 = Double

binPrintf :: PrintfType f => f
binPrintf = printf "%#x" -- 0x<lower-hex>

showB32bits :: Binary32 -> String
showB32bits = binPrintf . float2WordBitwise

showB64bits :: Binary64 -> String
showB64bits = binPrintf . double2WordBitwise

-- | @likelyReprAsSub32 c == (a, b)@ -> a - b ~= c
likelyReprAsSub32 :: Binary64 -> (Binary32, Binary32)
likelyReprAsSub32 b64 = (big, small)
    where big = double2Float b64
          small = fromRational $ toRational big - toRational b64 :: Binary32

-- | @fits64in32 b64@ <-> "shrinking" b64 to Binary32 does not round it
fits64in32 :: Binary64 -> Bool
fits64in32 b64 = toRational b64 == toRational (double2Float b64)

--------------------------------------------------------------------------------
-- | = (paranoid) Sanity checks
--------------------------------------------------------------------------------

floatToRational_correct :: RealFloat a => a -> Bool
floatToRational_correct f =
  toRational f == check
  where (mantissa, exponent) = decodeFloat f
        check = if exponent < 0
                then mantissa % (2 ^ (- toInteger exponent))
                else (mantissa * 2 ^ toInteger exponent) % 1

-- TODO: QuickCheck polymorphic?
prop_FloatToRational_correct32 :: Binary32 -> Bool
prop_FloatToRational_correct32 = floatToRational_correct

prop_FloatToRational_correct64 :: Binary64 -> Bool
prop_FloatToRational_correct64 = floatToRational_correct

prop_floatEq_exact32 :: Binary32 -> Bool
prop_floatEq_exact32 f =
  let f' = IEEE.nextUp f in
  let f'' = IEEE.nextDown f in
  f /= f' && not (f == f') && f < f' && f' > f
  &&
  f /= f'' && not (f == f'') && f'' < f && f > f''

prop_floatEq_exact64 :: Binary64 -> Bool
prop_floatEq_exact64 f =
  let f' = IEEE.nextUp f in
  let f'' = IEEE.nextDown f in
  f /= f' && not (f == f') && f < f' && f' > f
  &&
  f /= f'' && not (f == f'') && f'' < f && f > f''

-- | Float widening must preserve exact value
prop_float2Double_exact :: Binary32 -> Bool
prop_float2Double_exact b32 =
  toRational b32 == toRational (float2Double b32)

-- | Float shrinking must perform correct rounding
prop_double2Float_correct :: Binary64 -> Bool
prop_double2Float_correct b64 =
  double2Float b64 == (IEEE.fromRationalTiesToAway $ toRational b64 :: Binary32)

-- | Generic operators on Binary64 are as defined in IEEE-754
prop_Binary64OpIEEE :: Property
prop_Binary64OpIEEE =
       forallPb64   (\(x, y) -> x + y == IEEE.genericAdd x y)
  .&&. forallPb64   (\(x, y) -> x - y == IEEE.genericSub x y)
  .&&. forallPb64   (\(x, y) -> x * y == IEEE.genericMul x y)
  .&&. forallPb64nz (\(x, y) -> x / y == IEEE.genericDiv x y)
  where b64 = arbitrary :: Gen Binary64
        forallPb64 = forAll $ liftM2 (,) b64 b64
        forallPb64nz = forAll $ liftM2 (,) b64 (b64 `suchThat` (/= 0))

--------------------------------------------------------------------------------
-- | = Problem statement
--------------------------------------------------------------------------------

compute2ways :: Functor f => (forall a. RealFrac a => f a -> a) -> f Binary32 -> (Binary32, Binary32)
compute2ways f x32 =
  let
    -- the "real world" route
    x64 = float2Double <$> x32
    y64 = f x64
    y32_of_y64 = double2Float y64
    -- the "perfect world" route
    xr = toRational <$> x32
    yr = f xr
    y32_of_yr = IEEE.fromRationalTiesToEven yr
  in
    (y32_of_y64, y32_of_yr)

compute2ways_same :: Functor f => (forall a. RealFrac a => f a -> a) -> f Binary32 -> Bool
compute2ways_same f x = l == r
  where (l, r) = compute2ways f x

--------------------------------------------------------------------------------
-- | = DynWin
--------------------------------------------------------------------------------

-- Counterexample for polynomial correctness:
-- [a2, a1, a0, v] = [8.538427e-2,2.789586,9.182908,15.403517]
dynWinPoly :: RealFrac a => [a] -> a
dynWinPoly [a2, a1, a0, v] = (a2 * v * v) + (a1 * v) + a0
dynWinPoly _               = error "Runtime error. This is no Coq."

dynWinCheb :: RealFrac a => [a] -> a
dynWinCheb [rx, ry, ox, oy] = max (abs $ rx - ox) (abs $ ry - oy)
dynWinCheb _               = error "Runtime error. This is no Coq."

fullDynWin :: RealFrac a => [a] -> a
fullDynWin [a2, a1, a0, v, rx, ry, ox, oy] =
  if p < cheb
  then fromInteger 0
  else fromInteger 1
  where p = dynWinPoly [a2, a1, a0, v]
        cheb = dynWinCheb [rx, ry, ox, oy]
fullDynWin _               = error "Runtime error. This is no Coq."

genDynWinPoly :: Gen [Binary32]
genDynWinPoly = do
  -- a0 <- choose (0, 12.15) :: Gen Binary32
  -- a1 <- choose (0.01, 20.6) :: Gen Binary32
  -- a2 <- choose (0.0833333, 0.5) :: Gen Binary32
  vv <- choose (0, 20) :: Gen Binary32
  b <- choose (1, 6) :: Gen Binary32
  aa <- choose (0, 5) :: Gen Binary32
  e <- choose (0.01, 0.1) :: Gen Binary32
  let a0 = (aa/b + 1) * ((aa/2)*e*e + e*vv)
      a1 = vv/b + e*(aa/b + 1)
      a2 = 1/(2*b)
  v <- choose (0, 20) :: Gen Binary32
  pure [a2, a1, a0, v]

fullGenDynWin :: Gen [Binary32]
fullGenDynWin = do
  poly <- genDynWinPoly
  let coord_gen = choose (-5000, 5000)
  (rx, ry) <- liftM2 (,) coord_gen coord_gen
  (ox, oy) <- liftM2 (,) coord_gen coord_gen
  --- Try this instead for some counterexamples
  -- let (rx, ox) = likelyReprAsSub32 (dynWinPoly $ float2Double <$> poly)
  --     ry = fromIntegral 42
  --     oy = ry
  pure $ poly ++ [rx, ry, ox, oy]

prop_dynwin2ways_same :: Property
prop_dynwin2ways_same = forAll fullGenDynWin (compute2ways_same fullDynWin)

--------------------------------------------------------------------------------
-- | = GENERALIZED (random expressions)
--------------------------------------------------------------------------------

data Expr a =
  Const a
  | Abs (Expr a)
  | Add (Expr a) (Expr a)
  | Sub (Expr a) (Expr a)
  | Mul (Expr a) (Expr a)
  | Div (Expr a) (Expr a)
  | Min (Expr a) (Expr a)
  | Max (Expr a) (Expr a)
  deriving (Show, Functor)

evalExpr :: RealFrac a => Expr a -> a
evalExpr (Const x) = x
evalExpr (Abs x)   = abs $ evalExpr x
evalExpr (Add x y) = evalExpr x + evalExpr y
evalExpr (Sub x y) = evalExpr x - evalExpr y
evalExpr (Mul x y) = evalExpr x * evalExpr y
evalExpr (Div x y) = evalExpr x / evalExpr y
evalExpr (Min x y) = evalExpr x `min` evalExpr y
evalExpr (Max x y) = evalExpr x `max` evalExpr y

prettyPrintExpr :: Show a => Expr a -> String
prettyPrintExpr = go
  where go (Const x) = show x
        go (Abs x)   = "|" <> go x <> "|"
        go (Add x y) = bin " + " x y
        go (Sub x y) = bin " - " x y
        go (Mul x y) = bin " * " x y
        go (Div x y) = bin " / " x y
        go (Min x y) = bin " `min` " x y
        go (Max x y) = bin " `max` " x y
        bin s x y = "(" <> go x <> s <> go y <> ")"

--- NOTE: this doesn't @read@
-- instance Show a => Show (Expr a) where
--   show = prettyPrintExpr

instance Arbitrary a => Arbitrary (Expr a) where
  arbitrary = sized expr'
    where expr' 0 = Const <$> arbitrary
          expr' n = oneof [Abs <$> expr' (n - 1)
                          , Add <$> subexpr' <*> subexpr'
                          , Sub <$> subexpr' <*> subexpr'
                          , Mul <$> subexpr' <*> subexpr'
                          , Div <$> subexpr' <*> subexpr'
                          -- , Min <$> subexpr' <*> subexpr'
                          -- , Max <$> subexpr' <*> subexpr'
                          ]
            where subexpr' = expr' (n `div` 2)

prop_eval2ways_same :: Expr Binary32 -> Bool
prop_eval2ways_same = compute2ways_same evalExpr

--------------------------------------------------------------------------------
-- | = Run
--------------------------------------------------------------------------------

return []
runTests = $quickCheckAll

main :: IO ()
main = void runTests
