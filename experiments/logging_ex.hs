import Control.Monad.Writer  
    
type WInt = Writer [String] Int
    
wplus :: WInt -> WInt -> WInt
wplus wa wb = 
    do {
      a <- wa ;
      b <- wb ;
      tell ["plus " ++ show a ++ " " ++ show b] ;
      return (a+b)
    }

foo = (wplus
        (wplus (return 8) (return 2))
        (return 3)
       )
           
main = mapM_ putStrLn $ snd $ runWriter foo
       
             
