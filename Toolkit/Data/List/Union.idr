|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.List.Union

import public Decidable.Equality

import public Data.List.Elem

%default total

public export
data Union : (xs,ys,zs : List a) -> Type where
  End : Union Nil ys ys
  Pos : Elem x ys
     -> Union     xs  ys zs
     -> Union (x::xs) ys zs
  Neg : Not (Elem x ys)
     -> Union     xs  ys     zs
     -> Union (x::xs) ys (x::zs)

export
union : DecEq a
     => (xs,ys : List a)
              -> DPair (List a) (Union xs ys)

union [] ys
  = (ys ** End)

union (x :: xs) ys with (union xs ys)
  union (x :: xs) ys | (zs ** prf) with (isElem x ys)
    union (x :: xs) ys | (zs ** prf) | (Yes prfR)
      = (zs ** Pos prfR prf)
    union (x :: xs) ys | (zs ** prf) | (No contra)
      = (x :: zs ** Neg contra prf)


-- [ EOF ]
