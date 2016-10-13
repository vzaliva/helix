{- source https://stackoverflow.com/questions/13317242/what-are-paramorphisms -}

para :: (a -> [a] -> b -> b) -> b -> [a] -> b
para f base = h
  where
    h []       =   base
    h (x:xs)   =   f x xs (h xs)

para1  :: (a -> [a] -> b -> b) -> b -> [a] -> b
para1  c n (x : xs) = c x xs (para1 c n xs)
para1  c n []       = n
