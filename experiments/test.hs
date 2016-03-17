{-# LANGUAGE ScopedTypeVariables #-}

import Control.Monad.Identity
import Control.Monad.Writer
import Data.Monoid
import Data.Maybe
import Control.Monad.Trans.Maybe


{- Structural flag is Any: a Boolean monoid under conjunction ('&&'). -}
    
type W = Writer All
type WInt = W Int

struct :: a -> W a
struct x = return x

value :: a -> W a
value x = do tell (All False) ; return x
    
-- Regular plus, without collision checking
wplus :: WInt -> WInt -> WInt
wplus = liftM2 (+)
  
runW :: WInt -> (Int, Bool)
runW x = let (v,f) = runWriter x
         in (v, getAll f)

-- ex0 = runW (wplus (mzero) (return 2))
-- ex1 = runW (wplus (return 2) (mzero))

x :: WInt
x = value 2

y :: WInt
y = struct 2


ex0 = runW (wplus (struct 2) (struct 1))
ex1 = runW (wplus (struct 0) (value 2))
ex2 = runW (wplus (value 2) (struct 3))
    
ex3 = runW (wplus (value 1) (value 2))
ex4 = runW (wplus (value 0) (value 2))

ex5 = runW (wplus (wplus (value 1) (value 2)) (value 2))
ex6 = runW (wplus (wplus (value 0) (value 2)) (value 2))
ex7 = runW (wplus (wplus (value 1) (value 2)) (value 0))
ex8 = runW (wplus (wplus (struct 1) (value 2)) (struct 0))
ex9 = runW (wplus (wplus (struct 1) (struct 2)) (value 0)) -- collision!

