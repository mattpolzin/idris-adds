# Idris Additions

A collection of occasionally useful modules.

These modules are organized around the smallest useful units of functionality rather than collected under relevant types. This means you can take what you need and not need to spend time building against the rest. I'll call these micro-modules.

## List
The following micro-modules have general utility when working with lists.

### `Data.List.DeleteBy`
Offers the `deleteBy'` function that behaves like the `base` library's `Data.List.deleteBy` but it returns both the element that was deleted and the remaining list.

### `Data.List.IsElemBy`
Offers the `isElemBy` function that behaves like the `base` library's `Data.List.Elem.isElem` but it accepts a predicate instead of relying on equality to determine whether an element is in the list. It therefore decidably produces the element matched, the proof that the element matches the predicate, and the proof that the element is in the list (`Dec (x ** (p x = True, Elem x xs))`).

### `Data.List.PrefixSuffix`
Offers the `PrefixSuffix` type and the `dropPrefix`/`dropSuffix` functions that decidably divide lists into their prefix and suffix.

## Nat
The following micro-modules have general utility when working with natural numbers.

### `Data.Nat.MultReduces`
Offers `multReduces`, proof that the same number `y` multiplied by different multiplicands on either side of an equality presents an opportunity to reduce by some multiple of `y`.

## String
The following micro-modules have general utility when working with strings.

### `Data.String.NonEmpty`
Offers the `NonEmptyString` type and related functions, including a `fromString` function that allows you to create non empty strings with string literals.

## System
The following micro-modules have general utility when working with the operating system.

...

## Vect
The following micro-modules have general utility when working with vectors.

### `Data.Vect.Rotate`
Offers the `rotateTo` functions that rotates a vector so that some index in the vector is the new head of the vector. It is as if the vector is actually a ring and elements rotate off the front around to the back.

