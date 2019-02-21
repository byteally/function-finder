{-# OPTIONS_GHC -ddump-prep        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module HasFunction where

import Data.Kind
import Data.String
import GHC.TypeLits
import qualified Data.Proxy as P

data Proxy (x :: Symbol) = Proxy

class HasFunction (lab :: Symbol) (sig :: Type) where
  getFun :: Proxy lab -> sig

instance (Num a) => HasFunction "test" (a -> a) where
  getFun _ = bar

bar :: (Num a) => a -> a
bar = id

foo :: (Num a) => a -> a
foo = getFun (Proxy :: Proxy "test")

    
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
  MissingConstraints n tl tr =
    TypeError ('Text "Cannot match type " ':$$:
               'ShowType tl ':$$:
               'Text "With type " ':$$:
               'ShowType tr ':$$:
               'Text "while trying to use a binding: " ':$$:
               'ShowType n
              )

