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

We can combine both using Monad Trasnformers:
-}
    
type S = WriterT All (Writer Any)
type SInt = S Int

struct :: a -> S a
struct x = return x
    
value :: a -> S a
value x = do (tell (All False)) ; return x

v::SInt
v = value 2
s::SInt
s = struct 2
                                
runW :: SInt -> (Int, Bool, Bool)
runW x = let ((v, f), c) = runWriter (runWriterT x) in
         (v, getAll f, getAny c)

{- simple lifted (+), without collision tracking -}         
plus :: SInt -> SInt -> SInt
plus = liftM2 (+)

       
{- Union operator, which is basically (+) with collision tracking -}         
union :: SInt -> SInt -> SInt
union = plus

       
ex0 = runW (plus (struct 2) (struct 1))
ex1 = runW (plus (struct 0) (value 2))
ex2 = runW (plus (value 2) (struct 3))
ex3 = runW (plus (value 1) (value 2))
ex4 = runW (plus (value 0) (value 2))
ex5 = runW (plus (plus (value 1) (value 2)) (value 2))
ex6 = runW (plus (plus (value 0) (value 2)) (value 2))
ex7 = runW (plus (plus (value 1) (value 2)) (value 0))
ex8 = runW (plus (plus (struct 1) (value 2)) (struct 0))
      
ex9 = runW (plus (plus (struct 1) (struct 2)) (value 0)) -- untracked collision!
ex10 = runW (union (union (struct 1) (struct 2)) (value 0)) -- tracked collision

