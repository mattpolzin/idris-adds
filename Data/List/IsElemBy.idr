module Data.List.IsElemBy

import Data.So
import Data.List
import Data.List.Elem

%default total

neitherHereNorThere : {0 p : a -> Bool}
                   -> (notP : So (not (p x)))
                   -> (x' ** (p x' = True, Elem x' (x :: xs)))
                   -> (Not (x : a ** (p x = True, Elem x xs)))
                   -> Void
neitherHereNorThere notP (x' ** (p', Here))    f = soNotToNotSo notP $ eqToSo p'
neitherHereNorThere notP (x' ** (p', There y)) f = f (x' ** (p', y))

export
isElemBy : (p : a -> Bool) -> (xs : List a) -> Dec (x ** (p x = True, Elem x xs))
isElemBy p [] = No $ \(x ** (prf, el)) => absurd el
isElemBy p (x :: xs) with (choose (p x))
  isElemBy p (x :: xs) | (Left px) = rewrite sym $ soToEq px in Yes (x ** (Refl, Here))
  isElemBy p (x :: xs) | (Right notP) with (isElemBy p xs)
    isElemBy p (_ :: xs) | (Right notP) | (Yes (fst ** (prf, el))) = Yes $ (fst ** (prf, There el))
    isElemBy p (x :: xs) | (Right notP) | (No contra) = No $ \isElem => neitherHereNorThere notP isElem contra

