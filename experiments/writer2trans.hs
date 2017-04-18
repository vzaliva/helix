{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Control.Monad.Identity
import Control.Monad.Writer
import Test.HUnit

{- For Collisions -}

data Collision = C Bool

instance Monoid Collision where
    mempty =  C False
    mappend (C a) (C b) = C (a || b)

{- For structural -}

data Struct = S Bool

instance Monoid Struct where
    mempty =  S True
    mappend (S a) (S b) = S (a && b)

type CSInt = Writer Struct (Writer Collision Int)

struct :: Int -> CSInt
struct x = return $ return x
    
value :: Int -> CSInt
value x = do (tell (S False)) ; return $ return x

isStruct :: CSInt -> Bool
isStruct x = let (_, S s) = runWriter x in s


v::CSInt
v = value 2
s::CSInt
s = struct 2
                                
liftCSInt2 :: (Int -> Int -> Int) -> CSInt -> CSInt -> CSInt
liftCSInt2 f m1 m2 =
    let s1 = isStruct m1 in
    let s2 = isStruct m2 in
    do {
        cx1 <- m1;
        cx2 <- m2;
        return(
               do {
                 x1 <- cx1;
                 x2 <- cx2;
                 tell (C (not (s1||s2))) ;
                 return (f x1 x2)
               }
              )
    }

{- Union operator, which is basically (+) with collision tracking -}
union :: CSInt -> CSInt -> CSInt
union = liftCSInt2 (+)

testCases :: [(String, CSInt, (Int, Bool, Bool))]
testCases = [
 ("c1",  (union (struct 2) (struct 1)),                    (3,True,False)),
 ("c2",  (union (struct 0) (value 2)),                     (2,False,False)),
 ("c3",  (union (value 2) (struct 3)),                     (5,False,False)),
 ("c4",  (union (value 1) (value 2)),                      (3,False,True)),
 ("c5",  (union (value 0) (value 2)),                      (2,False,True)),
 ("c6",  (union (union (value 1) (value 2)) (value 2)),     (5,False,True)),
 ("c7",  (union (union (value 0) (value 2)) (struct 2)),    (4,False,True)),
 ("c8",  (union (union (struct 1) (value 2)) (value 0)),    (3,False,True)),
 ("c9",  (union (union (struct 10) (value 20)) (struct 0)), (30,False,False)),
 ("c10", (union (union (struct 1) (struct 9)) (value 0)),   (10,False,False)),
 ("c11", (union (union (struct 1) (struct 2)) (value 0)), (3,False,False))]

runW :: CSInt -> (Int, Bool, Bool)
runW x = let (t, S s) = runWriter x in
         let (v, C c) = runWriter t in
         (v, s, c)

runCases :: [(String, CSInt, (Int, Bool, Bool))] -> [Test]
runCases l = [TestCase $ assertEqual n b (runW a) | (n,a,b) <- l]

main :: IO Counts
main = runTestTT $ TestList (runCases testCases)
