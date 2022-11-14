||| A `list` construct to create lists of dependent types.
|||
||| One of the problems with using dependent types is that types
||| depend on values. This affects the ability to construct lists of
||| values that have a dependent type. The existing `List` type cannot
||| be used as it requires all elements to have the same type.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.DSnocList

import        Data.String
import public Data.SnocList
import public Data.SnocList.Elem


||| A list construct for dependent types.
|||
||| @aTy    The type of the value contained within the list element type.
||| @elemTy The type of the elements within the list
||| @as     The List used to contain the different values within the type.
public export
data DSnocList : (0 aTy    : Type)
              -> (0 elemTy : aTy -> Type)
              -> (  as     : SnocList aTy)
                          -> Type
  where
    ||| Create an empty List
    Lin : DSnocList aTy elemTy Lin
    ||| Cons
    |||
    ||| @elem The element to add
    ||| @rest The list for `elem` to be added to.
    (:<) : (rest : DSnocList aTy elemTy xs)
        -> (elem : elemTy x)
                -> DSnocList aTy elemTy (xs :< x)


public export
map : (f  : forall x . this x -> that x)
   -> (ts : DSnocList ty this sx)
         -> DSnocList ty that sx
map f Lin = Lin
map f (rest :< elem)
  = map f rest :< f elem

namespace SnocList
  public export
  map : (f  : forall x . e x -> b)
     -> (sx : DSnocList a e sy)
           -> SnocList b
  map f [<] = [<]
  map f (rest :< elem) = map f rest :< f elem


public export
lookup : (idx : Elem x xs)
      -> (ps  : DSnocList type pred xs)
             -> pred x
lookup Here (rest :< elem)
  = elem

lookup (There y) (rest :< elem)
  = lookup y rest


public export
replace : (idx : Elem x xs)
       -> (new : pred x)
       -> (ps  : DSnocList type pred xs)
              -> DSnocList type pred xs
replace Here new (rest :< elem)
  = rest :< new
replace (There y) new (rest :< elem)
  = replace y new rest :< elem


namespace Alt
  public export
  index : (xs  : DSnocList iTy eTy is)
       -> (idx : Elem i is)
       -> eTy i
  index sx xdi = lookup xdi sx

  public export
  update : (vs  : DSnocList iTy eTy is)
        -> (idx : Elem i is)
        -> (new : eTy i)
               -> DSnocList iTy eTy is
  update vs idx new = replace idx new vs


public export
updateWith : DSnocList iTy eTy is
          -> Elem i is
          -> (eTy i -> eTy i)
          -> DSnocList iTy eTy is
updateWith (rest :< ex) Here f
  = rest :< f ex
updateWith (rest :< ex) (There later) f
  = updateWith rest later f :< ex


||| Function to show a `DSnocList`.
|||
||| Due to limitations in idris wrt to class instances on dependent
||| types a generic show instance cannot be defined for
||| sigmalist. This will cause minor annoyances in its use.
|||
||| @showFunc A function to show the elements
||| @l       The list to be Shown.
public export
show : (showFunc : forall a . elemTy a -> String)
    -> (l        : DSnocList aTy elemTy as)
                -> String
show f xs = "[<" ++ unwords (reverse $ intersperse "," (toList $ SnocList.map f xs)) ++ "]"

-- --------------------------------------------------------------------- [ EOF ]
