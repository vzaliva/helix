
liftM2  :: (Monad m) => (a1 -> a2 -> r) -> m a1 -> m a2 -> m r
liftM2 f m1 m2 = do { x1 <- m1; x2 <- m2; return (f x1 x2) }

liftM2'  :: (Monad m) => (a1 -> a2 -> r) -> m a1 -> m a2 -> m r
liftM2' f m1 m2 =  m1 >>= (\x1 -> m2 >>= (\x2 -> return (f x1 x2)))
                             
{- https://wiki.haskell.org/All_About_Monads#The_Writer_monad -}
newtype Writer w a = Writer { runWriter :: (a,w) } 

instance (Monoid w) => Monad (Writer w) where 
    return a             = Writer (a,mempty) 
    (Writer (a,w)) >>= f = let (a',w') = runWriter $ f a in Writer (a',w `mappend` w')


                                         
