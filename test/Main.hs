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
import PolyKinded
-- default ()


caller1 :: Int -> Int
caller1 = getFun (Proxy :: Proxy "num")

caller2 :: [Int] -> String
caller2 = getFun (Proxy :: Proxy "showF")

caller3 :: Int -> String -> Int
caller3 = getFun (Proxy :: Proxy "num2")

caller4 :: Double -> Int -> Double
caller4 = getFun (Proxy :: Proxy "num4")

showF :: (Show a) => a -> String
showF = show

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

main = defaultMain $ do
  testGroup "callers" [ test_caller1
                      , test_caller2
                      , test_caller3
                      , test_caller4
                      ]
test_caller1 = testCase "caller1" (caller1 10 @?= 74)
test_caller2 = testCase "caller2" (caller2 [1,2,3] @?= "[1,2,3]")
test_caller3 = testCase "caller3" (caller3 25 "foo" @?= 25)
test_caller4 = testCase "caller4" (caller4 36.5 25 @?= 61.5)
    
