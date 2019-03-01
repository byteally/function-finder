{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleInstances    #-}

module PolyKinded where

import Data.Kind
import Data.Proxy

type family TF (a :: k) :: Type where
  TF (a :: Bool) = Bool
  TF (a :: Type) = Int

class TFCls (a :: k) where
  tfmeth :: Proxy a -> (TF a -> TF a)

instance TFCls (a :: Bool) where
  tfmeth _ = id

tffun :: TF 'True -> TF 'True
tffun = tfmeth (Proxy :: Proxy 'True)

test_id :: a -> String
test_id = const "ffo"

class MethTest (a :: Type) where
  methTest :: a -> String

instance MethTest Int where
  methTest = show

