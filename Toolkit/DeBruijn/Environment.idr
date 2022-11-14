||| Environments.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.DeBruijn.Environment

import Decidable.Equality

import Data.DPair

import Toolkit.Decidable.Informative

import Toolkit.Data.SnocList.AtIndex
import Toolkit.Data.DSnocList
import Toolkit.Data.DSnocList.AtIndex

import Toolkit.DeBruijn.Context.Item
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming

%default total

||| Sometimes it is bettern to think that we have this thing called an
||| environment and not a `DList`.
|||
||| @t    The Type for Types in our environment.
||| @obj  How we interpret the types in our DSL. Either this is a
|||       dependent type or a function that computes a type.
||| @ctxt The typing context.
public export
Env : (0 t    : Type)
   -> (0 obj  : t -> Type)
   -> (  ctxt : SnocList t)
             -> Type
Env = DSnocList

||| Add an object to our execution environment.
||| @env The typing environment.
export
extend : (env : Env ty e ctxt)
      -> (obj : e t)
      -> Env ty e (ctxt :< t)
extend = (:<)

namespace Elem
  ||| Read an object from our typing environment.
  |||
  ||| @idx Which object.
  ||| @env The execution environment.
  export
  read : (idx : Elem t ctxt)
      -> (env : Env ty e ctxt)
      -> e t
  read = lookup

  ||| Add an object to our execution environment.
  |||
  ||| @idx Where the object is.
  ||| @obj The new object.
  ||| @env The environment to which the object is added.
  export
  update : (idx : Elem t ctxt)
        -> (obj : e t)
        -> (env : Env ty e ctxt)
        -> Env ty e ctxt
  update = replace

namespace IsVar
  ||| Read an object from our typing environment.
  |||
  ||| @idx Which object.
  ||| @env The execution environment.
  export
  read : (idx : IsVar ctxt t)
      -> (env : Env ty e ctxt)
      -> e t
  read (V 0 Here) (rest :< elem)
    = elem
  read (V (S idx) (There later)) (rest :< elem)
    = read (V idx later) rest

  ||| Add an object to our execution environment.
  |||
  ||| @idx Where the object is.
  ||| @obj The new object.
  ||| @env The environment to which the object is added.
  export
  update : (idx : IsVar ctxt t)
        -> (obj : e t)
        -> (env : Env ty e ctxt)
        -> Env ty e ctxt
  update (V 0 Here) obj (rest :< elem)
    = rest :< obj
  update (V (S k) (There later)) obj (rest :< elem)
    = update (V k later) obj rest :< elem

-- [ EOF ]
