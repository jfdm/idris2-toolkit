||| Error returning quantifiers for Vectors
|||
||| Module    : Quantifiers.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Toolkit.Data.Vect.Quantifiers

import public Toolkit.Decidable.Informative
import        Data.Vect

import        Data.Vect.Quantifiers

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
      -> (xs  : Vect n a)
              -> DecInfo Error (All p xs)
  all' _ _ []
    = Yes []

  all' pos f (x :: xs) with (f x)
    all' pos f (x :: xs) | (Yes pH) with (all' (S pos) f xs)
      all' pos f (x :: xs) | (Yes pH) | (Yes pT)
        = Yes (pH :: pT)
      all' pos f (x :: xs) | (Yes pH) | (No pR c)
        = No pR
             (notAllThere c)

    all' pos f (x :: xs) | (No contra)
      = No (MkError pos)
           (notAllHere contra)

  export
  all : (f  : (x : a)
                -> Dec (p x))
     -> (xs : Vect n a)
            -> DecInfo Error (All p xs)
  all = all' Z


-- [ EOF ]
