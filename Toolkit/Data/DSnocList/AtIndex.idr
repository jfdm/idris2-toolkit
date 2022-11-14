||| Reasoning about elements in a DList based on their index.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.DSnocList.AtIndex

import Decidable.Equality

import Toolkit.Decidable.Informative

import Toolkit.Data.SnocList.AtIndex
import Toolkit.Data.DSnocList

%default total

||| Proof that some element satisfies the predicate
|||
||| @idx   The type of the element's index.
||| @type  The type of the list element.
||| @p     A predicate
||| @xs      The list itself.
public export
data HoldsAtIndex : (0 type   : Type)
                 -> (0 item   : type -> Type)
                 -> (0 p      : forall i . (x : item i) -> Type)
                 -> {  is     :  SnocList type}
                 -> (  xs     : DSnocList type item is)
                 -> (  idx    : Nat)
                           -> Type
    where
      ||| Proof that the element is at the front of the list.
      Here : {0 p   : forall i . (x : item i) -> Type}
          -> (  prf : p x)
                   -> HoldsAtIndex type item p (xs :< x) Z


      ||| Proof that the element is found later in the list.
      There : {0 p      : forall i . (x : item i) -> Type}
           -> (contra : p x' -> Void)
           -> (later  : HoldsAtIndex type item p  xs          loc)
                     -> HoldsAtIndex type item p (xs :< x) (S loc)

namespace Find
  namespace HoldsAtIndex
    public export
    data Error type = IsEmpty
                    | Later type (HoldsAtIndex.Error type)



isEmpty : {0 p  : forall i . (x : item i) -> Type}
       -> DPair Nat (HoldsAtIndex type item p Lin)
       -> Void
isEmpty (MkDPair loc prf) with (prf)
  isEmpty (MkDPair loc prf) | (MkDPair _ (Here _)) impossible
  isEmpty (MkDPair loc prf) | (MkDPair _ (There _)) impossible


export
holdsAtIndex : {0 p  : forall i . (x : item i) -> Type}
            -> (  f  : forall i . (x : item i) -> DecInfo err (p x))
            -> (  xs : DSnocList type item is)
                    -> DecInfo (HoldsAtIndex.Error err)
                               (DPair Nat (HoldsAtIndex type item p xs))
holdsAtIndex f [<]
  = No IsEmpty isEmpty

holdsAtIndex f (rest :< elem) with (f elem)
  holdsAtIndex f (rest :< elem) | (Yes prf)
    = Yes (0 ** Here prf)

  holdsAtIndex f (rest :< elem) | (No msg no) with (holdsAtIndex f rest)
    holdsAtIndex f (rest :< elem) | (No msg no) | (Yes (loc ** prf))
      = Yes (S loc ** There no prf)

    holdsAtIndex f (rest :< elem) | (No msg no) | (No msgL noR)
      = No (Later msg msgL)
           (\case (0 ** (Here prf)) => no prf
                  ((S loc) ** (There contra later)) => noR (loc ** later))

-- [ EOF ]
