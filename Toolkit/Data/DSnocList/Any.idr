||| The Any list quantifier for the DList quantifier.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.DSnocList.Any

import Toolkit.Decidable.Informative

import Toolkit.Data.DSnocList

import public Toolkit.Decidable.Equality.Indexed

%default total


||| Proof that some element satisfies the predicate
|||
||| @idx   The type of the element's index.
||| @type  The type of the list element.
||| @p     A predicate
||| @xs      The list itself.
public export
data Any : (0 idx  : Type)
        -> (0 type : idx -> Type)
        -> (0 p    : forall i . (x : type i) -> Type)
        -> {  is   : SnocList idx}
        -> (  xs   : DSnocList idx type is)
                  -> Type
    where
      ||| Proof that the element is at the front of the list.
      H : {0 p   : forall i . (x : type i) -> Type}
       -> (  prf : p y)
                -> Any idx type p (xs :< y)

      ||| Proof that the element is found later in the list.
      T : {0 p      : forall i . (x : type i) -> Type}
       -> (  contra : p x' -> Void)
       -> (  later  : Any idx type p       xs)
                   -> Any idx type p (xs :< x')

{0 p : forall i . (x : type i) -> Type} -> Uninhabited (Any idx type p Lin) where
  uninhabited (H prf) impossible
  uninhabited (T contra later) impossible

export
any : {0 p  : forall i . (x : type i) -> Type}
   -> (  f  : forall i . (x : type i) -> DecInfo err (p x))
   -> (  xs : DSnocList idx type is)
           -> Dec (Any idx type p xs)
any f [<]
  = No absurd

any f (rest :< elem) with (f elem)
  any f (rest :< elem) | (Yes prf)
    = Yes (H prf)

  any f (rest :< elem) | (No msg no) with (any f rest)
    any f (rest :< elem) | (No msg no) | (Yes prf)
      = Yes (T no prf)
    any f (rest :< elem) | (No msg no) | (No contra)
      = No (\case (H prf) => no prf
                  (T g later) => contra later)

-- [ EOF ]
