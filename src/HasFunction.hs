{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module HasFunction where

import Data.Kind
import GHC.TypeLits
import Data.Proxy

class HasFunction (lab :: Symbol) (sig :: Type) where
  getFun :: Proxy lab -> sig

type family BindingNotFound (s :: Symbol) :: Constraint where
  BindingNotFound s =
    TypeError ('Text "A (local) binding with name: " ':$$:
               'ShowType s ':$$:
               'Text "was not found in scope"
              )
               
type family MissingConstraints (ps :: Constraint) (n :: Symbol) :: Constraint where
  MissingConstraints ps s =
    (TypeError ('Text "Following constraints could not be resolved: " ':$$:
               'ShowType ps ':$$:
               'Text "while trying to use a binding: " ':$$:
               'ShowType s
              )
    , ps)

type family CannotMatchType (n :: Symbol) (tl :: Type) (tr :: Type) :: Constraint where
  CannotMatchType n tl tr =
    TypeError ('Text "Cannot match type " ':$$:
               'ShowType tl ':$$:
               'Text "With type " ':$$:
               'ShowType tr ':$$:
               'Text "while trying to use a binding: " ':$$:
               'ShowType n
              )

