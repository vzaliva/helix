{-# LANGUAGE ScopedTypeVariables #-}

import Control.Monad.Identity
import Control.Monad.Writer
import Data.Monoid
import Data.Maybe
import Control.Monad.Trans.Maybe

data Structural a = Value a | Struct a deriving (Show)  

instance Monad Structural where
    return = Value
    Struct x >>= k = k x
    Value x >>= k = case (k x) of
                      Struct y -> Value y
                      Value y -> Value y -- fail "could not combine values"


type WInt = Structural Int

union :: WInt -> WInt -> WInt
union = liftM2 (+)
    
runW :: WInt -> WInt
runW x = x

x :: WInt
x = return 5
             
ex0 = runW (union (Struct 2) (Struct 1))
ex1 = runW (union (Struct 0) (return 2))
ex2 = runW (union (return 2) (Struct 3))

ex3 = runW (union (return 1) (return 2))
ex4 = runW (union (return 0) (return 2))

ex5 = runW (union (union (return 1) (return 2)) (return 2))
ex6 = runW (union (union (return 0) (return 2)) (return 2))
ex7 = runW (union (union (return 1) (return 2)) (return 0))

