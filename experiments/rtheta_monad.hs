{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Control.Monad.Identity
import Control.Monad.Writer
import Test.HUnit

data Flags = F Bool Bool

{- Collision-tracking monoid -}

newtype XFlags = XF Flags

instance Monoid XFlags where
    mempty =  XF (F True False)
    (XF (F s0 c0)) `mappend` (XF (F s1 c1)) = XF (F (s0 && s1)
                                    (c0 || c1 || not (s0 || s1)))
 
type XInt = WriterT XFlags Identity Int

{- Union operator, which is basically (+) with structural and collision tracking -}         
union :: XInt -> XInt -> XInt
union = liftM2 (+)

{- Alternative, "safe" Monoid: -}

newtype SFlags = SF Flags
    
instance Monoid SFlags where
    mempty =  SF (F True False)
    (SF (F s0 c0)) `mappend` (SF (F s1 c1)) = SF (F (s0 && s1) (c0 || c1))

type SInt = WriterT SFlags Identity Int
                                            
{- Safe Union operator, which is basically (+) with structural tracking, but without collision tracking -}         
sunion :: SInt -> SInt -> SInt
sunion = liftM2 (+)

{- experimental -}

sFromX :: XInt -> SInt
sFromX = mapWriter (\(x, XF fs) -> (x, SF fs))

xFromS :: SInt -> XInt
xFromS = mapWriter (\(x, SF fs) -> (x, XF fs))

{- convinience functoins -}
         
xstruct :: Int -> XInt
xstruct x = return x
    
xvalue :: Int -> XInt
xvalue x = do (tell (XF (F False False))) ; return x

sstruct :: Int -> SInt
sstruct x = return x
    
svalue :: Int -> SInt
svalue x = do (tell (SF (F False False))) ; return x
                                          
{- Unit tests -}

runW :: XInt -> (Int, Bool, Bool)
runW x = let (v, (XF (F s c))) = runIdentity (runWriterT x) in
         (v, s, c)
         
testCases :: [(String, WriterT XFlags Identity Int, (Int, Bool, Bool))]
testCases = [
 ("x1",  (union (xstruct 2) (xstruct 1)),                    (3,True,False)),
 ("x2",  (union (xstruct 0) (xvalue 2)),                     (2,False,False)),
 ("x3",  (union (xvalue 2) (xstruct 3)),                     (5,False,False)),
 ("x4",  (union (xvalue 1) (xvalue 2)),                      (3,False,True)),
 ("x5",  (union (xvalue 0) (xvalue 2)),                      (2,False,True)),
 ("s5",  xFromS (sunion (svalue 0) (svalue 2)),              (2,False,False)),
 ("s6",  xFromS (sunion (sstruct 1) (svalue 2)),             (3,False,False)),
 ("x6",  (union (union (xvalue 1) (xvalue 2)) (xvalue 2)),     (5,False,True)),
 ("x7",  (union (union (xvalue 0) (xvalue 2)) (xstruct 2)),    (4,False,True)),
 ("x8",  (union (union (xstruct 1) (xvalue 2)) (xvalue 0)),    (3,False,True)),
 ("x9",  (union (union (xstruct 1) (xvalue 2)) (xstruct 0)),   (3,False,False)),
 ("x10", (union (union (xstruct 1) (xstruct 2)) (xvalue 0)),   (3,False,False)),
 ("x11", (union (union (xstruct 1) (xstruct 2)) (xvalue 0)), (3,False,False))]

runCases :: [(String, XInt, (Int, Bool, Bool))] -> [Test]
runCases l = [TestCase $ assertEqual n (runW a) b | (n,a,b) <- l]

main :: IO Counts
main = runTestTT $ TestList (runCases testCases)
