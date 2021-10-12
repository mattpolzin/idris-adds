module Data.Nat.MultReduces

import Data.Nat

%default total

||| If you have the same thing multiplied by different values on either side of
||| an equality, you can reduce by plucking the thing off each side until one side
||| reaches 0. This function also allows for some additional amount added to one
||| side of the equality.
|||
||| If `(x * y) + z = n * y` then you can factor out a certain number of `y`s (specifically
||| `k` of them) from both sides such that either `z = k * y` or `k * y + z = 0`.
||| 
||| It is perhaps easier to see how this is reduction over multiplication in the
||| specific case where `z = 0`: Then the result is that either `0 = k * y` or
||| `k * y = 0`.
multReduces : {y,z : Nat} -> {n : Nat} -> {x : Nat} 
           -> (x * y) + z = n * y 
           -> Either (k ** z = k * y) (k ** k * y + z = 0)
multReduces {n=0} {x=x} = Right . (MkDPair _)
multReduces {n=n} {x=0} = Left . (MkDPair _)
multReduces {n=(S k)} {x=(S j)} = 
  rewrite sym $ plusAssociative y (j * y) z in 
    \prf => let prf' = plusLeftCancel y ((j * y) + z) (k * y) prf in
                multReduces prf'

