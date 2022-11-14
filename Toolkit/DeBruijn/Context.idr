|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.DeBruijn.Context

import Decidable.Equality

import Data.DPair
import Data.Singleton

import Data.SnocList
import Data.SnocList.Quantifiers

import Toolkit.Decidable.Informative

import public Toolkit.Data.SnocList.AtIndex

import public Toolkit.Data.DSnocList
import        Toolkit.Data.DSnocList.AtIndex

import public Toolkit.DeBruijn.Context.Item

%default total

public export
Context : (0 kind : Type) -> (types : SnocList kind) -> Type
Context kind = DSnocList kind Item


export
extend : (ctxt  : Context kind types)
      -> (label : String)
      -> (type  : kind)
               -> Context kind (types :< type)
extend ctxt label type
  = ctxt :< I label type

||| A quantifier over the context that the given predicate holds.
|||
||| This is modelled after De Bruijn indices, and the underlying
||| quantifier is `Any`.
|||
public export
data Exists : (0 kind  : Type)
           -> (0 pred  : (type : kind) -> Type)
           -> (  key   : String)
           -> (  types : SnocList kind)
           -> (  ctxt  : Context kind types)
                      -> Type
  where
    E : -- {ctxt : Context kind types}
        {0 pred : (type : kind) -> Type}
     -> (type : kind)
     -> (item : Item type)
     -> (prf  : pred type)
     -> (locC : HoldsAtIndex kind Item (Holds kind pred key) ctxt loc)
     -> (locN : AtIndex type types loc)
             -> Exists kind pred key types ctxt

public export
data DeBruijn : (0 kind  : Type)
             -> (types   : SnocList kind)
             -> (ctxt    : Context kind types)
                        -> Type
  where
    DB : (type : kind)
      -> (idx  : AtIndex type types loc)
              -> DeBruijn kind types ctxt

export
deBruijn : (prf  : Exists kind pred key types ctxt)
                -> DeBruijn kind types ctxt

deBruijn (E type item prf locC locN)
  = DB type locN


namespace Exists
  public export
  data Error type = NotFound
                  | NotSatisfied type

Uninhabited (Exists kind pred key Lin Lin) where
  uninhabited (E _ _ _ _ Here) impossible
  uninhabited (E _ _ _ _ (There later)) impossible


notLater : (Holds  kind pred key       h  -> Void)
        -> (Exists kind pred key ts  t       -> Void)
        ->  Exists kind pred key (ts :< t') (t :< h)
        -> Void
notLater f g (E type item prf (Here x) locN)
  = f x
notLater f g (E type item prf (There contra later) (There x))
  = g (E type item prf later x)


export
exists : (func  : (type : kind) -> DecInfo err (pred type))
      -> (key   : String)
      -> (ctxt  : Context kind types)
               -> DecInfo (Exists.Error err)
                          (Exists kind pred key types ctxt)
exists f key [<]
  = No NotFound absurd

exists f key (t :< h) with (holds f key h)
  exists f key (t :< (I str x)) | (Yes (H prfK prf))
    = Yes (E x (I str x) prf (Here (H prfK prf)) Here)

  exists f key (t :< h) | (No msg no) with (exists f key t)
    exists f key (t :< h) | (No msg no) | (Yes (E type item prf locC locN))
      = Yes (E type item prf (There no locC) (There locN))

    -- [ Note ]
    --
    -- we need to ensure that the 'correct' error message is propagated..

    exists f key (t :< h) | (No (NotSatisfied x) no) | (No msgT noT)
      = No (NotSatisfied x)
           (notLater no noT)

    exists f key (t :< h) | (No (WrongName str str1) no) | (No msgT noT)
      = No msgT
           (notLater no noT)


namespace Lookup

  public export
  IsBound : (key   : String)
         -> (types : SnocList kind)
         -> (ctxt  : Context kind types)
                  -> Type
  IsBound {kind} str types ctxt
    = Exists kind Singleton
                str
                types
                ctxt

  single : (item : kind)
                -> DecInfo () (Singleton item)
  single item = Yes (Val item)


  export
  lookup : (str   : String)
        -> (ctxt  : Context kind types)
                 -> DecInfo (Exists.Error ())
                            (IsBound str types ctxt)
  lookup = exists single

export
rebuild : (f  : a -> String)
       -> (as : SnocList a)
             -> Context a as
rebuild _ [<]
  = [<]

rebuild f (xs :< x)
  = rebuild f xs :< I (f x) x


-- [ EOF ]
