{-# LANGUAGE TypeApplications
           , TemplateHaskell
           , MultiParamTypeClasses
#-}
import Test.QuickCheck
import Data.List (sort, nub)
import qualified Data.Set as S

class IsList l where
  rev :: l a -> l a

class Specification l where
  (<~) :: (Ord a) => l a -> l a -> Bool

class Abstract l' l where
  abstract :: (Ord a) => l a -> l' a 


instance IsList [] where
  rev xs = reverse xs


data Interval a = IA { lower :: Int , upper :: Int }
instance Abstract Interval [] where
  abstract xs = IA (length xs) (length xs)
instance Specification Interval where
  ia <~ ia' = lower ia' <= lower ia && upper ia <= upper ia'
instance IsList Interval where
  rev = id


data Elements a = Elems { elms :: S.Set a }
instance Abstract Elements [] where
  abstract = Elems . foldr S.insert S.empty 
instance Specification Elements where
  ia <~ ia' = elms ia == elms ia'
instance IsList Elements where
  rev = id
