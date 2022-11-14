|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.DList.Union

import public Decidable.Equality

import public Data.List.Elem

import public Toolkit.Data.List.Union

import public Toolkit.Data.DList


%default total


public export
data Union : (xs : DList a p ps)
          -> (ys : DList a p ps')
          -> (zs : DList a p ps'')
          -> (prf : Union ps ps' ps'') -> Type
  where
    End : Union Nil ys ys End
    Pos : {xs : DList a p ps}
       -> {ys : DList a p ps'}
       -> Union     xs  ys zs            rest
       -> Union (x::xs) ys zs (Pos prf' rest)
    Neg : {xs : DList a p ps}
       -> {ys : DList a p ps'}
       -> Union     xs  ys     zs            rest
       -> Union (x::xs) ys (x::zs) (Neg prf' rest)


union' : (xs  : DList a p ps)
      -> (ys  : DList a p ps')
      -> (prf : Union ps ps' ps'')
             -> (zs : DList a p ps'' ** Union xs ys zs prf)
union' [] ys End
  = (ys ** End)

union' (elem :: rest) ys (Pos x y) with (union' rest ys y)
  union' (elem :: rest) ys (Pos x y) | (zs ** prf)
    = (zs ** Pos prf)

union' (elem :: rest) ys (Neg f x) with (union' rest ys x)
  union' (elem :: rest) ys (Neg f x) | (zs ** prf)
    = (elem :: zs ** Neg prf)

export
union : DecEq a
     => {ps, ps' : _}
     -> (xs  : DList a p ps)
     -> (ys  : DList a p ps')
            -> (ps'' : List a ** zs : DList a p ps''     **
                prf : Union ps ps' ps'' ** Union xs ys zs prf)
union {ps} {ps'} xs ys with (Toolkit.Data.List.Union.union ps ps')
  union {ps = ps} {ps' = ps'} xs ys | (zs ** prf) with (union' xs ys prf)
    union {ps = ps} {ps' = ps'} xs ys | (zs ** prf) | (rest ** prf') = (zs ** rest ** prf ** prf')


-- [ EOF ]
