{-# LANGUAGE ScopedTypeVariables #-}

import Control.Monad.Identity
import Control.Monad.Writer
import Data.Monoid
import Data.Maybe
import Control.Monad.Trans.Maybe


{- Structural flag is All: a Boolean monoid under conjunction ('&&'). 
The initial value is 'True' and values are combined using &&.
-}
    
type W = Writer All
type WInt = W Int

struct :: a -> W a
struct x = return x

value :: a -> W a
value x = do tell (All False) ; return x
    
-- Regular plus, without collision checking
plus :: WInt -> WInt -> WInt
plus = liftM2 (+)
  
runW :: WInt -> (Int, Bool)
runW x = let (v,f) = runWriter x
         in (v, getAll f)

x :: WInt
x = value 2

y :: WInt
y = struct 2


ex0 = runW (plus (struct 2) (struct 1))
ex1 = runW (plus (struct 0) (value 2))
ex2 = runW (plus (value 2) (struct 3))
    
ex3 = runW (plus (value 1) (value 2))
ex4 = runW (plus (value 0) (value 2))

ex5 = runW (plus (plus (value 1) (value 2)) (value 2))
ex6 = runW (plus (plus (value 0) (value 2)) (value 2))
ex7 = runW (plus (plus (value 1) (value 2)) (value 0))
ex8 = runW (plus (plus (struct 1) (value 2)) (struct 0))
ex9 = runW (plus (plus (struct 1) (struct 2)) (value 0)) -- collision!

