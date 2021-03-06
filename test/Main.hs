-- {-# OPTIONS_GHC -dcore-lint               #-}
{-# OPTIONS_GHC -ddump-prep                #-}
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
import Data.Bool
import qualified Data.Maybe as M
-- default ()

caller1 :: Int -> Int
caller1 = getFun (Proxy :: Proxy "num")

caller2 :: [Int] -> String
caller2 = getFun (Proxy :: Proxy "showF")

caller3 :: Int -> String -> Int
caller3 = getFun (Proxy :: Proxy "num2")

caller4 :: Double -> Int -> Double
caller4 = getFun (Proxy :: Proxy "num4")

caller5 :: Int -> String
caller5 = getFun (Proxy :: Proxy "show")

caller6 :: Int -> Int -> Int
caller6 = getFun (Proxy :: Proxy "+")

caller7 :: Bool -> Bool
caller7 = getFun (Proxy :: Proxy "not")

caller8 :: Bool -> Bool
caller8 = getFun (Proxy :: Proxy "id")

caller9 :: [Bool] -> [Bool] -> [Bool]
caller9 = getFun (Proxy :: Proxy "++")

caller10 :: Bool -> Bool -> Bool
caller10 = getFun (Proxy :: Proxy "||")

caller11 :: Int -> String
caller11 = getFun (Proxy :: Proxy "test_id")

caller12 :: Maybe a -> Bool
caller12 = getFun (Proxy :: Proxy "M.isJust")

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
                      , test_caller5
                      , test_caller6
                      , test_caller7
                      , test_caller8
                      , test_caller9
                      , test_caller10
                      , test_caller11
                      , test_caller12
                      ]
test_caller1 = testCase "caller1" (caller1 10 @?= 74)
test_caller2 = testCase "caller2" (caller2 [1,2,3] @?= "[1,2,3]")
test_caller3 = testCase "caller3" (caller3 25 "foo" @?= 25)
test_caller4 = testCase "caller4" (caller4 36.5 25 @?= 61.5)
test_caller5 = testCase "caller5" (caller5 20 @?= "20")
test_caller6 = testCase "caller6" (caller6 20 30 @?= 50)
test_caller7 = testCase "caller7" (caller7 True @?= False)
test_caller8 = testCase "caller8" (caller8 True @?= True)
test_caller9 = testCase "caller9" (caller9 [True, False] [False, True] @?= [True, False, False, True])
test_caller10 = testCase "caller10" (caller10 True False @?= True)
test_caller11 = testCase "caller11" (caller11 20 @?= "ffo")
test_caller12 = testCase "caller12" (caller12 (Just 'c') @?= True)

               
