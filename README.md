# Idris Additions

A collection of occasionally useful modules.

These modules are organized around the smallest useful units of functionality rather than collected under relevant types. This means you can take what you need and not need to spend time building against the rest. I'll call these micro-modules.

This package currently supports Idris 2 versions 0.4.0, 0.5.1, and the nightly builds.

Install this package by running `make install`. Use it by depending upon `idris-adds` with `idris2 -p idris-adds` or by specifying in your ipkg's `depends` list.

## List
The following micro-modules have general utility when working with lists.

### DeleteBy [(src)](./Data/List/DeleteBy.idr)
Offers the `deleteBy'` function that behaves like the `base` library's `Data.List.deleteBy` but it returns both the element that was deleted and the remaining list.

### IsElemBy [(src)](./Data/List/IsElemBy.idr)
Offers the `isElemBy` function that behaves like the `base` library's `Data.List.Elem.isElem` but it accepts a predicate instead of relying on equality to determine whether an element is in the list. It therefore decidably produces the element matched, the proof that the element matches the predicate, and the proof that the element is in the list (`Dec (x ** (p x = True, Elem x xs))`).

### PrefixSuffix [(src)](./Data/List/PrefixSuffix.idr)
Offers the `PrefixSuffix` type and the `dropPrefix`/`dropSuffix` functions that decidably divide lists into their prefix and suffix.

## Nat
The following micro-modules have general utility when working with natural numbers.

### MultReduces [(src)](./Data/Nat/MultReduces.idr)
Offers `multReduces`, proof that the same number `y` multiplied by different multiplicands on either side of an equality presents an opportunity to reduce by some multiple of `y`.

## Pagination [(src)](./Data/Pagination.idr)
The `Pagination` module offers a type representing the pagination of data and utility functions for working with it.

For example, if you want to represent meta pages (i.e. the structure of pages without content on them) for an API request you might create a pagination that splits 100 items up with 10 items on each page and then traverse over the pagination making API requests for each page:
```idris
let pgs : PaginationShape 100 10 _ = metaPages 100 10
in  traverse' (\perPage,pageIdx,_,_ => apiRequest (perPage * pageIdx) perPage) pgs
```

You also might want to take 100 items and paginate them similarly:
```idris
let pgs : Pagination 100 10 _ (List Int) = pages [1..100] 10
in  traverse printLn pgs
```

## String
The following micro-modules have general utility when working with strings.

### NonEmpty [(src)](./Data/String/NonEmpty.idr)
Offers the `NonEmptyString` type and related functions, including a `fromString` function that allows you to create non empty strings with string literals.

## System
The following micro-modules have general utility when working with the operating system.

...

## Vect
The following micro-modules have general utility when working with vectors.

### Rotate [(src)](./Data/Vect/Rotate.idr)
Offers the `rotateTo` functions that rotates a vector so that some index in the vector is the new head of the vector. It is as if the vector is actually a ring and elements rotate off the front around to the back.

