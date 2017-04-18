{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Control.Monad.Identity
import Control.Monad.Writer
import Test.HUnit

{- 
Structural flag is 'All': a Boolean monoid under conjunction ('&&'). 
The initial value is 'True' and values are combined using &&.

Collision flag is 'Any': A Boolean monoind under disjunction ('||').
The initial value is 'False' and values are combined using ||

F (flags) type combines structural and collision flags
-}

data Flags = F Bool Bool

{- Collision-tracking monoid -}

newtype RFlags = XF Flags

instance Monoid RFlags where
    mempty =  XF (F True False)
    (XF (F s0 c0)) `mappend` (XF (F s1 c1)) = XF (F (s0 && s1)
                                    (c0 || c1 || not (s0 || s1)))
 
type XInt = Writer RFlags Int

{- Union operator, which is basically (+) with structural and collision tracking -}         
union :: XInt -> XInt -> XInt
union = liftM2 (+)

{- Alternative, "safe" Monoid: -}

newtype XFlags = SF Flags
    
instance Monoid XFlags where
    mempty =  SF (F True False)
    (SF (F s0 c0)) `mappend` (SF (F s1 c1)) = SF (F (s0 && s1) (c0 || c1))

type SInt = Writer XFlags Int
                                            
{- Safe Union operator, which is basically (+) with structural tracking, but without collision tracking -}         
sunion :: SInt -> SInt -> SInt
sunion = liftM2 (+)

{- convinience functoins -}
         
struct :: Int -> XInt
struct x = return x
    
value :: Int -> XInt
value x = do (tell (XF (F False False))) ; return x

{- Unit tests -}

runW :: XInt -> (Int, Bool, Bool)
runW x = let (v, (XF (F s c))) = runWriter x in
         (v, s, c)
         
testCases :: [(String, WriterT RFlags Identity Int, (Int, Bool, Bool))]
testCases = [
 ("c1",  (union (struct 2) (struct 1)),                    (3,True,False)),
 ("c2",  (union (struct 0) (value 2)),                     (2,False,False)),
 ("c3",  (union (value 2) (struct 3)),                     (5,False,False)),
 ("c4",  (union (value 1) (value 2)),                      (3,False,True)),
 ("c5",  (union (value 0) (value 2)),                      (2,False,True)),
 ("c6",  (union (union (value 1) (value 2)) (value 2)),     (5,False,True)),
 ("c7",  (union (union (value 0) (value 2)) (struct 2)),    (4,False,True)),
 ("c8",  (union (union (struct 1) (value 2)) (value 0)),    (3,False,True)),
 ("c9",  (union (union (struct 1) (value 2)) (struct 0)),   (3,False,False)),
 ("c10", (union (union (struct 1) (struct 2)) (value 0)),   (3,False,False)),
 ("c11", (union (union (struct 1) (struct 2)) (value 0)), (3,False,False))]

runCases :: [(String, XInt, (Int, Bool, Bool))] -> [Test]
runCases l = [TestCase $ assertEqual n (runW a) b | (n,a,b) <- l]

main :: IO Counts
main = runTestTT $ TestList (runCases testCases)
