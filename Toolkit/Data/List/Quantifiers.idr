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
    namespace NotAll
      public export
      data NotAll : (p  : (x : type) -> Type)
                 -> (e  : Type)
                 -> (xs : List type)
                       -> Type
        where
          Here : (msg : e)
              -> (prf : p x -> Void)
                     -> NotAll p e (x::xs)

          There : {0 p     : (a : type) -> Type}
               -> (  prf   :        p    x)
               -> (  later : NotAll p e     xs)
                          -> NotAll p e (x::xs)

    export
    position : NotAll p e xs -> Nat
    position (Here _ _)
      = Z
    position (There _ later)
      = S (position later)

  export
  all : (f  : (x : a)
                -> DecInfo e (p x))
     -> (xs : List a)
           -> DecInfo (NotAll p e xs)
                      (All    p   xs)
  all f []
    = Yes []

  all f (x :: xs) with (f x)
    all f (x :: xs) | (Yes pH) with (all f xs)
      all f (x :: xs) | (Yes pH) | (Yes pT)
        = Yes (pH :: pT)

      all f (x :: xs) | (Yes pH) | (No m c)
        = No (There pH m)
             (\(y::ys) => c ys)

    all f (x :: xs) | (No m c)
      = No (Here m c)
           (\(y::ys) => c y)

-- [ EOF ]
