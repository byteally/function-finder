{-# OPTIONS_GHC -dcore-lint               #-}
{-# OPTIONS_GHC -ddump-prep               #-}
{-# OPTIONS_GHC -fplugin ConstraintSolver #-}
{-# LANGUAGE MultiParamTypeClasses        #-}
{-# LANGUAGE KindSignatures               #-}
{-# LANGUAGE DataKinds                    #-}
{-# LANGUAGE FlexibleContexts             #-}

import Data.Kind
import GHC.TypeLits
import HasFunction
import Data.String
import Test.Tasty
import Test.Tasty.HUnit
import Data.Proxy
-- default ()

caller2 :: (Num a) => a -> a
caller2 = getFun (Proxy :: Proxy "num")


{-
caller1 :: Int -> Int
caller1 = getFun (Proxy :: Proxy "num")
-}

baz :: Int -> Int
baz = (+ 35)

zap :: Int -> Int
zap = (+ 64)

num :: (Num a) => a -> a
num = (+ 64)

num2 :: (Num a, Show b) => a -> b -> a
num2 a _ = a

num4 :: (Num a, Num b, Integral b) => a -> b -> a
num4 a b = a + (fromIntegral b)

num4Test :: (Num a) => a -> a -> a
num4Test a b = a + b

num3 :: (Num a, Show b, IsString c) => a -> b -> String -> c
num3 a _ s = fromString s

consti :: a -> Int
consti _ = 25

const2i :: a -> b -> a
const2i a _ = a

const2C :: String -> Int -> Int
const2C _ a = a

fail :: Int -> ()
fail = const ()

xings = show (5 :: Int)

proBool :: Proxy (x :: Bool) -> ()
proBool _ = ()


main = pure ()
{-
defaultMain $
  testCase "caller1" $ do
    caller1 5 @?= 69
-}
