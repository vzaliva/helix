{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Control.Monad.Identity
import Control.Monad.Writer
import Data.Monoid
import Data.Maybe
import Control.Monad.Trans.Maybe


{- Structural flag is All: a Boolean monoid under conjunction ('&&'). 
The initial value is 'True' and values are combined using &&.

So simple structural Writer monad is:
    
 type W = Writer All
 type WInt = W Int

Collision flag is Any: A Boolean monoind under disjunction ('||').
The initial value is 'False' and values are combined using ||

F (flags) type combines structural and collision flags
-}

data F = F Bool Bool

instance Monoid F where
    mempty =  F True False
    (F s0 c0) `mappend` (F s1 c1) = F (s0 && s1)
                                    (c0 || c1 || not (s0 || s1))

type S = Writer F
type SInt = S Int

struct :: a -> S a
struct x = return x
    
value :: a -> S a
value x = do (tell (F False False)) ; return x

v::SInt
v = value 2
s::SInt
s = struct 2
                                
runW :: SInt -> (Int, Bool, Bool)
runW x = let (v, (F s c)) = runWriter x in
         (v, s, c)
         
{- simple lifted (+), without collision tracking -}         
plus :: SInt -> SInt -> SInt
plus = liftM2 (+)

       
{- Union operator, which is basically (+) with collision tracking -}         
union :: SInt -> SInt -> SInt
union = plus

       
ex0 = runW (plus (struct 2) (struct 1))
ex1 = runW (plus (struct 0) (value 2))
ex2 = runW (plus (value 2) (struct 3))
ex3 = runW (plus (value 1) (value 2)) -- coll
ex4 = runW (plus (value 0) (value 2)) -- coll
ex5 = runW (plus (plus (value 1) (value 2)) (value 2)) -- coll
ex6 = runW (plus (plus (value 0) (value 2)) (struct 2)) -- coll
ex7 = runW (plus (plus (struct 1) (value 2)) (value 0)) -- coll
ex8 = runW (plus (plus (struct 1) (value 2)) (struct 0))

ex9 = runW (plus (plus (struct 1) (struct 2)) (value 0)) 
ex10 = runW (union (union (struct 1) (struct 2)) (value 0)) 

