import Control.Monad.Writer  
    
type WInt = Writer Bool Int

instance Monoid Bool where
    mempty =  False
    mappend  = (||)
    
wplus :: WInt -> WInt -> WInt
wplus wa wb = 
    do {
      a <- wa ;
      b <- wb ;
      tell (a == 0 || b==0) ;
      return (a+b)
    }

foo = (wplus
        (wplus (return 1) (return 2))
        (return 3)
       )
           
main = putStrLn $ show $ snd $ runWriter foo
       
             
