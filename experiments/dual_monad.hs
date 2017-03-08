{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

import Control.Monad.Writer
import Test.HUnit
import Control.Comonad
import Data.Functor.Identity

{- Utils -}
{- see http://stackoverflow.com/questions/27342863/unsequence-monad-function-within-haskell -}
unsequence :: (Comonad w, Monad m) => w [a] -> [m a]
unsequence = (map return) . extract

{- For Collisions -}

data Collision = C Bool

instance Eq Collision where
    (==) (C a) (C b) = a==b

instance Show Collision where
    show (C x) = "C " ++ show x

instance Monoid Collision where
    mempty =  C False
    mappend (C a) (C b) = C (a || b)

{- For structural -}

data Struct = S Bool

instance Eq Struct where
    (==) (S a) (S b) = a==b

instance Show Struct where
    show (S x) = "S " ++ show x

instance Monoid Struct where
    mempty =  S True
    mappend (S a) (S b) = S (a && b)

type SM = Writer Struct
type SInt = SM Int
type CM = Writer Collision
type CSInt = CM SInt

{- TODO: Make sure it satisfies co-monad laws:
see https://github.com/ekmett/comonad

extend extract      = id
extract . extend f  = f
extend f . extend g = extend (f . extend g)

-}
instance (Monoid w) => Comonad (Writer w) where
    {- extract :: Writer w a -> a -}
    extract x = fst $ runWriter x
    {- extend :: (Writer w a -> b) -> Writer w a -> Writer w b -}
    extend f wa = do { tell $ execWriter wa ; return (f wa)}
    {- duplicate x = do { tell $ execWriter x ; return x}  -}

sstruct :: Int -> SInt
sstruct x = return x

csstruct :: Int -> CSInt
csstruct x = return $ sstruct x

svalue :: Int -> SInt
svalue x = do (tell (S False)) ; return x

csvalue :: Int -> CSInt
csvalue x = return $ svalue x

isStruct :: SInt -> Bool
isStruct x = let (_, S s) = runWriter x in s

mkCollision :: t -> Writer Collision t
mkCollision x = do (tell (C True)) ; return x

v::CSInt
v = csvalue 2
s::CSInt
s = csstruct 2

liftCSInt2 :: (Int -> Int -> Int) -> CSInt -> CSInt -> CSInt
liftCSInt2 f m1 m2 = do {
                       s1 <- m1 ;
                       s2 <- m2 ;
                       tell (C (not (isStruct s1 || isStruct s2))) ;
                       return $liftM2 f s1 s2
                     }

{- Union operator, which is basically (+) with collision tracking -}
union :: CSInt -> CSInt -> CSInt
union = liftCSInt2 (+)

{- Simple map2 wich we will use as an example underlying function to lift
   in various ways -}
map2 :: (a->b->c) -> [a] -> [b] -> [c]
map2 f a b = map (\(x,y) -> f x y) $ zip a b

foldSM :: [CSInt] -> CM [SInt]
foldSM = sequence

itemizeSM :: CM [SInt] -> [CSInt]
itemizeSM a = let (l,f) = runWriter a in
              map (\x -> do { tell f ; return x}) l

{- umap2 :: SM [SInt] -> SM [SInt] -> SM [SInt]
umap2 a b = liftM2 (map2 union) -}

{- Unit tests below -}

csintTestCases :: [(String, CSInt, (Int, Bool, Bool))]
csintTestCases = [
 ("runW1", csvalue  1, (1,False,False)),
 ("runW2", csstruct 1, (1,True,False)),
 ("union1",  (union (csstruct 2) (csstruct 1)),                    (3,True,False)),
 ("union2",  (union (csstruct 0) (csvalue 2)),                     (2,False,False)),
 ("union3",  (union (csvalue 2) (csstruct 3)),                     (5,False,False)),
 ("union4",  (union (csvalue 1) (csvalue 2)),                      (3,False,True)),
 ("union5",  (union (csvalue 0) (csvalue 2)),                      (2,False,True)),
 ("union6",  (union (union (csvalue 1) (csvalue 2)) (csvalue 2)),     (5,False,True)),
 ("union7",  (union (union (csvalue 0) (csvalue 2)) (csstruct 2)),    (4,False,True)),
 ("union8",  (union (union (csstruct 1) (csvalue 2)) (csvalue 0)),    (3,False,True)),
 ("union9",  (union (union (csstruct 10) (csvalue 20)) (csstruct 0)), (30,False,False)),
 ("union10", (union (union (csstruct 1) (csstruct 9)) (csvalue 0)),   (10,False,False)),
 ("union11", (union (union (csstruct 1) (csstruct 2)) (csvalue 0)),   (3,False,False)),
 ("mkCollision1", mkCollision (svalue 1), (1,False,True)),
 ("mkCollision2", mkCollision (sstruct 1), (1,True,True))]

runW :: CSInt -> (Int, Bool, Bool)
runW x = let (t, C c) = runWriter x in
         let (v, S s) = runWriter t in
         (v, s, c)

foldTestCases = [
 TestCase $ assertEqual "foldSM1"
          (C False)
          (execWriter (foldSM [csvalue 1, csvalue 2])),
 TestCase $ assertEqual "foldSM2"
          (C False)
          (execWriter (foldSM [csstruct 1, csvalue 2])),
 TestCase $ assertEqual "foldSM3"
          (C True)
          (execWriter (foldSM [mkCollision $ sstruct 1, csvalue 2])),
 TestCase $ assertEqual "foldSM4"
          (C False)
          (execWriter (foldSM [csstruct 1, csstruct 2]))]

itemizeTestCases = [
 TestCase $ assertEqual "itemize1"
          [(1,False,False),(2,False,False)]
          (map runW (itemizeSM $ return [svalue 1, svalue 2])),
 TestCase $ assertEqual "itemize2"
          [(1,False,True),(2,False,True)]
          (map runW (itemizeSM $ mkCollision [svalue 1, svalue 2]))]

runCases :: [(String, CSInt, (Int, Bool, Bool))] -> [Test]
runCases l = [TestCase $ assertEqual n b (runW a) | (n,a,b) <- l]

allcases = (runCases csintTestCases) ++ foldTestCases ++ itemizeTestCases

main :: IO Counts
main = runTestTT $ TestList allcases
