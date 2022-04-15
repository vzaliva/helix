#!/usr/bin/env stack
{- stack
  runghc
  --package QuickCheck
  --package fp-ieee
  --package floating-bits
-}

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




-- | = AUX

type Binary32 = Float
type Binary64 = Double

binPrintf :: PrintfType f => f
binPrintf = printf "%#x" -- 0x<lower-hex>

showB32bits :: Binary32 -> String
showB32bits = binPrintf . float2WordBitwise

showB64bits :: Binary64 -> String
showB64bits = binPrintf . double2WordBitwise



-- | (paranoid) SANITY CHECKS

floatToRational_correct :: RealFloat a => a -> Bool
floatToRational_correct b64 =
  toRational b64 == check
  where (mantissa, exponent) = decodeFloat b64
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

prop_addIEEE_correct32 :: Binary32 -> Binary32 -> Bool
prop_addIEEE_correct32 x y = x + y == IEEE.genericAdd x y

prop_addIEEE_correct64 :: Binary64 -> Binary64 -> Bool
prop_addIEEE_correct64 x y = x + y == IEEE.genericAdd x y

prop_mulIEEE_correct32 :: Binary32 -> Binary32 -> Bool
prop_mulIEEE_correct32 x y = x * y == IEEE.genericMul x y

prop_mulIEEE_correct64 :: Binary64 -> Binary64 -> Bool
prop_mulIEEE_correct64 x y = x * y == IEEE.genericMul x y



-- | = PROBLEM STATEMENT

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



-- | = PROBLEM PARAMETERS

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

prop_compute2ways_same_dynwin :: Property
prop_compute2ways_same_dynwin = forAll genDynWin computeDynWin2ways_same



-- | = TEST

return []
runTests = $quickCheckAll

main :: IO ()
main = void runTests
