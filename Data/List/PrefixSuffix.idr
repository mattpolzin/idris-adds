module Data.List.PrefixSuffix

import Data.List
import Decidable.Equality

%default total

||| Store a list as a suffix appended to a prefix.
public export
data PrefixSuffix : (0 prefixList : List a) -> (0 suffixList : List a) -> (0 fullList : List a) -> Type where
  Split : (prefixList : List a) -> (suffixList : List a) -> PrefixSuffix prefixList suffixList (prefixList ++ suffixList)

public export
prefixSuffixConsInjective : PrefixSuffix (x :: xs) suffixList (y :: ys) -> (x = y, PrefixSuffix xs suffixList ys)
prefixSuffixConsInjective (Split (x :: xs) suffixList) = (Refl, Split xs suffixList)

||| Cons the given element onto the list.
||| This operation necessarily conses the same element onto the prefix.
public export
cons : (y : _) -> PrefixSuffix xs suffixList ys -> PrefixSuffix (y :: xs) suffixList (y :: ys)
cons y (Split xs suffixList) = Split (y :: xs) suffixList

||| Take all but the first element of the list.
||| This operation necessarily drops the first element of the prefix.
public export
tail : PrefixSuffix (y :: xs) suffixList (y :: ys) -> PrefixSuffix xs suffixList ys 
tail (Split (y :: xs) suffixList) = Split xs suffixList

public export
fullListIsPrefixPlusSuffix : PrefixSuffix prefixList suffixList fullList -> prefixList ++ suffixList = fullList
fullListIsPrefixPlusSuffix (Split _ _) = Refl

public export
(.prefix) : {0 prefixList : List a} -> PrefixSuffix prefixList suffixList fullList -> List a
(.prefix) (Split ps _) = ps

public export
(.suffix) : {0 suffixList : List a} -> PrefixSuffix prefixList suffixList fullList -> List a
(.suffix) (Split _ ss) = ss

||| Reconstruct the full list from the prefix and suffix.
|||
||| If you make the `fullList` index of the `PrefixSuffix` runtime relevant, that
||| is an alternative way to recover the full list that does not involve appending
||| the suffix to the prefix at runtime.
public export
(.value) : {0 fullList : List a} -> PrefixSuffix prefixList suffixList fullList -> List a
(.value) (Split prefixList suffixList) = prefixList ++ suffixList

-- NonEmpty prefix & empty fullList
export
Uninhabited (PrefixSuffix (x :: xs) suffixList []) where
  uninhabited (Split (x :: xs) suffixList) impossible

listPlusNonEmptyListNotEmpty : {xs : _} -> Not (xs ++ (y :: ys) = [])
listPlusNonEmptyListNotEmpty {xs = []} prf = absurd prf
listPlusNonEmptyListNotEmpty {xs = (x :: xs)} prf = absurd prf

-- NonEmpty suffix & empty fullList
export
{prefixList : _} -> Uninhabited (PrefixSuffix prefixList (x :: xs) []) where
  uninhabited prefSuf with (fullListIsPrefixPlusSuffix prefSuf)
    uninhabited prefSuf | prf = listPlusNonEmptyListNotEmpty prf

prefixDifferentVoid : Not (x = y) -> Not (suffixList ** PrefixSuffix (x :: xs) suffixList (y :: ys))
prefixDifferentVoid contra (_ ** (Split (x :: xs) _)) = contra Refl

||| Drop a prefix from the given full list if possible.
export
dropPrefix : DecEq a => 
             (prefixList : List a) 
          -> (fullList : List a) 
          -> Dec (suffixList ** PrefixSuffix prefixList suffixList fullList)
dropPrefix [] fullList =
  Yes (fullList ** Split [] fullList)
dropPrefix (x :: xs) [] =
  No (\(l ** r) => absurd r)
dropPrefix (x :: xs) (y :: ys) with (decEq x y)
  dropPrefix (x :: xs) (y :: ys) | (No contra) =
    No (prefixDifferentVoid contra)
  dropPrefix (x :: xs) (x :: ys) | (Yes Refl) with (dropPrefix xs ys)
    dropPrefix (x :: xs) (x :: ys) | (Yes Refl) | (No contra) =
      No (\(suffixList ** prf) => contra (suffixList ** snd $ prefixSuffixConsInjective prf))
    dropPrefix (x :: xs) (x :: (xs ++ zs)) | (Yes Refl) | (Yes (zs ** Split xs zs)) = 
      Yes (zs ** Split (x :: xs) zs)

prefixReifies : (pfxSfx : PrefixSuffix pfx sfx full) -> pfxSfx.prefix = pfx
prefixReifies (Split pfx sfx) = Refl

suffixReifies : (pfxSfx : PrefixSuffix pfx sfx full) -> pfxSfx.suffix = sfx
suffixReifies (Split pfx sfx) = Refl

lemma : {w : _}
     -> Not ((x :: xs) = (y :: ys))
     -> Not (prefixList ** PrefixSuffix prefixList (x :: xs) ys) 
     -> Not (PrefixSuffix w (x :: xs) (y :: ys))
lemma {w = []} f g z with (fullListIsPrefixPlusSuffix z)
  lemma {w = []} f g z | contra = f contra
lemma {w = (w :: ws)} f g z with (fst . consInjective $ fullListIsPrefixPlusSuffix z)
  lemma {w = (w :: ws)} f g z | Refl = g (ws ** tail {y=w} z)

absurdXsYs : {0 xs, ys : List _} -> Not (x = y) -> Not (x :: xs = y :: ys)
absurdXsYs f Refl = f Refl

absurdXsYs' : {0 xs,ys : List _} -> Not (xs = ys) -> Not (x :: xs = y :: ys)
absurdXsYs' f Refl = f Refl

||| Drop a suffix from the given full list if possible.
export
dropSuffix : DecEq a => 
             (suffixList : List a) 
          -> (fullList : List a) 
          -> Dec (prefixList ** PrefixSuffix prefixList suffixList fullList)
-- empty suffix or empty full list
dropSuffix [] fullList =
  Yes (fullList ** rewrite sym $ appendNilRightNeutral fullList in Split fullList [])
dropSuffix (x :: xs) [] =
  No (\(_ ** contra) => absurd contra)
-- equal suffix and full list
dropSuffix (x :: xs) (y :: ys) with (decEq x y)
  dropSuffix (x :: xs) (y :: ys) | (Yes xEqY) with (decEq xs ys)
    dropSuffix (x :: xs) (x :: xs) | (Yes Refl) | (Yes Refl) =
      Yes ([] ** Split [] (x :: xs))
    -- rest of full list ends with suffix
    dropSuffix (x :: xs) (y :: ys) | (Yes xEqY) | (No contra) with (dropSuffix (x :: xs) ys)
      dropSuffix (x :: xs) (y :: ys) | (Yes xEqY) | (No xsNotYs) | (Yes (prefixList ** prf)) =
        Yes (y :: prefixList ** y `cons` prf)
      -- rest of full does not end with suffix
      dropSuffix (x :: xs) (y :: ys) | (Yes xEqY) | (No xsNotYs) | (No restNotSuffix) =
        No (\contra => lemma (absurdXsYs' xsNotYs) restNotSuffix (snd contra))
  -- rest of full list ends with suffix
  dropSuffix (x :: xs) (y :: ys) | (No xNotY) with (dropSuffix (x :: xs) ys)
    dropSuffix (x :: xs) (y :: ys) | (No xNotY) | (Yes (prefixList ** prf)) =
      Yes (y :: prefixList ** y `cons` prf)
    -- rest of full list does not end with suffix
    dropSuffix (x :: xs) (y :: ys) | (No xNotY) | (No restNotSuffix) =
      No (\contra => lemma (absurdXsYs xNotY) restNotSuffix (snd contra))

