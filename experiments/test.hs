import Control.Monad.Identity
import Control.Monad.Writer
import Data.Monoid    

type WInt = Writer Any Int
    
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
                  
ex0 = runWriter (bplus 1 2) 
ex1 = runWriter (bplus 0 2)

ex2 = runWriter (wbplus (return 1) (return 2))
ex3 = runWriter (wbplus (return 0) (return 2))

ex4 = runWriter (wbplus (wbplus (return 1) (return 2)) (return 2))
ex5 = runWriter (wbplus (wbplus (return 0) (return 2)) (return 2))
ex6 = runWriter (wbplus (wbplus (return 1) (return 2)) (return 0))
