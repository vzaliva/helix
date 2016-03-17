{-# LANGUAGE ScopedTypeVariables #-}
import Control.Monad.Identity
import Control.Monad.Writer
import Data.Monoid
import Data.Maybe
import Control.Monad.Trans.Maybe

type W = MaybeT (WriterT Any Identity)
type WInt = W Int

-- Regular plus, without collision checking
wplus :: WInt -> WInt -> WInt
wplus = liftM2 (+)
    
wbplus :: WInt -> WInt -> WInt
wbplus wa wb =
    do
      a <- wa ;
      b <- wb ;
      tell (Any (a == 0 || b == 0)) ;
           return (a+b)


runW :: WInt -> (Maybe Int, Bool)
runW x = let (v,f) = runWriter $ runMaybeT x
         in (v, getAny f)
                  
ex0 = runW (wbplus (mzero) (return 2))
ex1 = runW (wbplus (return 2) (mzero))

ex2 = runW (wbplus (return 1) (return 2))
ex3 = runW (wbplus (return 0) (return 2))

ex4 = runW (wbplus (wbplus (return 1) (return 2)) (return 2))
ex5 = runW (wbplus (wbplus (return 0) (return 2)) (return 2))
ex6 = runW (wbplus (wbplus (return 1) (return 2)) (return 0))

