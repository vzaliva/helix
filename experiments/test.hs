import Control.Monad.Identity
import Control.Monad.Writer
import Data.Monoid
import Data.Maybe

type W = WriterT Any Identity
type WInt = W Int
    
bplus :: Int -> Int -> WInt
bplus a b =
    do
      tell (Any (a == 0 || b == 0)) ;
           return (a+b)

wbplus :: WInt -> WInt -> WInt
wbplus wa wb =
    do
      a <- wa ;
      b <- wb ;
      tell (Any (a == 0 || b == 0)) ;
           return (a+b)

runW :: WInt -> (Int, Bool)
runW x = let (v,f) = runWriter x
         in (v,getAny f)
                  
ex0 = runW (bplus 1 2) 
ex1 = runW (bplus 0 2)

ex2 = runW (wbplus (return 1) (return 2))
ex3 = runW (wbplus (return 0) (return 2))

ex4 = runW (wbplus (wbplus (return 1) (return 2)) (return 2))
ex5 = runW (wbplus (wbplus (return 0) (return 2)) (return 2))
ex6 = runW (wbplus (wbplus (return 1) (return 2)) (return 0))
      
