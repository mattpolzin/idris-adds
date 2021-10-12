module Data.Vect.Rotate

import Data.Vect
import Data.Vect.Elem
import Data.Nat

%default total

export
rotateTo' : {m : _} -> (xs : Vect m a) -> (e : Elem x xs) -> (acc : Vect n a) -> Vect (m + n) a
rotateTo' (x :: xs) Here acc = (x :: xs) ++ (reverse acc)
rotateTo' {m=(S k)} (y :: xs) (There later) acc = rewrite plusSuccRightSucc k n in rotateTo' xs later (y :: acc)

||| The index given will be the new head of the vector.
|||
||| The input xs will be rotated such that the element e
||| is the head of the output with all the elements in
||| the same order, as if the vector was rotated while its
||| tail was connected to its head.
export
rotateTo : {n : _} -> (xs : Vect n a) -> (e : Elem x xs) -> Vect n a
rotateTo xs e = rewrite sym $ plusZeroRightNeutral n in rotateTo' xs e []

namespace Elem
  ||| Rotate the given index in the context of the given vector.
  |||
  ||| The offset determines the new head after rotation and the
  ||| index will be made into the rotated vector. This means the
  ||| index will have the same numeric value but a different
  ||| element.
  export
  rotateTo : {n : _} -> (xs : Vect n a) -> (offset : Elem x xs) -> (index : Elem y xs) -> (zs : Vect n a ** z ** Elem z zs)
  rotateTo xs offset index = let idx = elemToFin index 
                                 rotated = Vect.Rotate.rotateTo xs offset in
                                 (rotated ** indexElem idx rotated)

