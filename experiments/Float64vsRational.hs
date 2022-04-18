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

compute2ways :: (forall a. RealFrac a => [a] -> a) -> [Binary32] -> (Binary32, Binary32)
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

compute2ways_same :: (forall a. RealFrac a => [a] -> a) -> [Binary32] -> Bool
compute2ways_same f x = l == r
  where (l, r) = compute2ways f x

--------------------------------------------------------------------------------
-- | = DynWin
--------------------------------------------------------------------------------

dynWin :: RealFrac a => [a] -> a
dynWin [a2, a1, a0, v] = (a2 * v * v) + (a1 * v) + a0
dynWin _               = error "Runtime error. This is no Coq."

computeDynWin2ways_same :: [Binary32] -> Bool
computeDynWin2ways_same = compute2ways_same dynWin

genDynWin :: Gen [Binary32]
genDynWin = do
  a0 <- choose (0, 12.15)
  a1 <- choose (0.01, 20.6)
  a2 <- choose (0.0833333, 0.5)
  v <- choose (0, 20)
  pure [a2, a1, a0, v]

prop_dynwin2ways_same :: Property
prop_dynwin2ways_same = forAll genDynWin computeDynWin2ways_same

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

-- instance Show a => Show (Expr a) where
--   show = prettyPrintExpr

instance Arbitrary a => Arbitrary (Expr a) where
  arbitrary = resize 6 $ sized expr'
    where expr' 0 = Const <$> resize maxBound arbitrary
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
prop_eval2ways_same e32 =
  let
    -- the "real world" route
    e64 = float2Double <$> e32
    v64 = evalExpr e64
    v32_of_v64 = double2Float v64
    -- the "perfect world" route
    er = toRational <$> e32
    vr = evalExpr er
    v32_of_vr = IEEE.fromRationalTiesToEven vr
  in
    v32_of_v64 == v32_of_vr

--------------------------------------------------------------------------------
-- | = Run
--------------------------------------------------------------------------------

return []
runTests = $quickCheckAll

main :: IO ()
main = void runTests
