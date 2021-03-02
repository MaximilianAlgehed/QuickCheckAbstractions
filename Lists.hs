{-# LANGUAGE TypeApplications
           , TemplateHaskell
           , MultiParamTypeClasses
#-}
import Test.QuickCheck hiding (Sorted)
import qualified Data.List as L
import qualified Data.Set as S

class IsList l where
  rev :: l a -> l a
  append :: Ord a => l a -> l a -> l a
  sort :: Ord a => l a -> l a

class Specification l where
  (<~) :: (Ord a) => l a -> l a -> Bool

class Abstract l' l where
  abstract :: (Ord a) => l a -> l' a 


-- TODO: Try it out on some bugs
instance IsList [] where
  rev xs = reverse xs
  append xs ys = xs ++ ys
  sort xs = L.sort xs


data Interval a = IA { lower :: Int , upper :: Int }
instance Abstract Interval [] where
  abstract xs = IA (length xs) (length xs)
instance Specification Interval where
  ia <~ ia' = lower ia' <= lower ia && upper ia <= upper ia'
instance IsList Interval where
  rev = id
  append ia ia' = IA (lower ia + lower ia') (upper ia + upper ia')
  sort = id


data Elements a = Elems { elms :: S.Set a }
instance Abstract Elements [] where
  abstract = Elems . foldr S.insert S.empty 
instance Specification Elements where
  ia <~ ia' = elms ia == elms ia'
instance IsList Elements where
  rev = id
  append xs ys = Elems (elms xs `S.union` elms ys)
  sort = id


data Sorted a = Sorted { isSorted :: Bool }
instance Abstract Sorted [] where
  abstract xs = Sorted . and $ zipWith (<=) xs (tail xs)
instance Specification Sorted where
  ia <~ ia' = (not $ isSorted ia') || isSorted ia
instance IsList Sorted where
  rev xs = Sorted False
  append xs ys = Sorted False
  sort xs = Sorted True



prop_rev_abstract_interval :: [Int] -> Bool
prop_rev_abstract_interval xs = abstract @Interval (rev xs) <~ rev (abstract xs)

prop_append_abstract_interval :: [Int] -> [Int] -> Bool
prop_append_abstract_interval xs ys = abstract @Interval (append xs ys) <~ append (abstract xs) (abstract ys)

prop_sort_abstract_interval :: [Int] -> Bool
prop_sort_abstract_interval xs = abstract @Interval (sort xs) <~ sort (abstract xs)

prop_rev_abstract_elems :: [Int] -> Bool
prop_rev_abstract_elems xs = abstract @Elements (rev xs) <~ rev (abstract xs)

prop_append_abstract_elems :: [Int] -> [Int] -> Bool
prop_append_abstract_elems xs ys = abstract @Elements (append xs ys) <~ append (abstract xs) (abstract ys)

prop_sort_abstract_elems :: [Int] -> Bool
prop_sort_abstract_elems xs = abstract @Elements (sort xs) <~ sort (abstract xs)

prop_rev_abstract_sorted :: [Int] -> Bool
prop_rev_abstract_sorted xs = abstract @Sorted (rev xs) <~ rev (abstract xs)

prop_append_abstract_sorted :: [Int] -> [Int] -> Bool
prop_append_abstract_sorted xs ys = abstract @Sorted (append xs ys) <~ append (abstract xs) (abstract ys)

prop_sort_abstract_sorted :: [Int] -> Bool
prop_sort_abstract_sorted xs = abstract @Sorted (sort xs) <~ sort (abstract xs)

return []
test = $forAllProperties (quickCheckWithResult (stdArgs { maxSuccess = 10000 }))
