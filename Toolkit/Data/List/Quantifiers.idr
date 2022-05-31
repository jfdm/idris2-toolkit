||| Error returning quantifiers for Lists
|||
||| Module    : Quantifiers.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Toolkit.Data.List.Quantifiers

import public Toolkit.Decidable.Informative

import        Data.List.Quantifiers

%default total

namespace Informative

  namespace All
    public export
    record Error where
      constructor MkError
      firstFound : Nat

  all' : (pos : Nat)
      -> (f   : (x : a)
                  -> Dec (p x))
      -> (xs  : List a)
             -> DecInfo Error (All p xs)
  all' _ _ []
    = Yes []

  all' pos f (x :: xs) with (f x)
    all' pos f (x :: xs) | (Yes pH) with (all' (S pos) f xs)
      all' pos f (x :: xs) | (Yes pH) | (Yes pT)
        = Yes (pH :: pT)
      all' pos f (x :: xs) | (Yes pH) | (No pR c)
        = No pR
             (\(y::ys) => c ys)

    all' pos f (x :: xs) | (No contra)
      = No (MkError pos)
           (\(y::ys) => contra y)

  export
  all : (f  : (x : a)
                -> Dec (p x))
     -> (xs : List a)
           -> DecInfo Error (All p xs)
  all = all' Z


-- [ EOF ]
