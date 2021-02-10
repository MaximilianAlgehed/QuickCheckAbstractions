{-# LANGUAGE TypeApplications, TemplateHaskell, MultiParamTypeClasses #-}
import Test.QuickCheck
import Data.List (sort, nub)

class Tree t where
  empty :: t k v
  insert :: Ord k => k -> v -> t k v -> t k v
  delete :: Ord k => k -> t k v -> t k v
  merge :: Ord k => t k v -> t k v -> t k v

class Specification t where
  (<~) :: (Ord k , Ord v) => t k v -> t k v -> Bool

class Abstract t' t where
  abstract :: (Ord k, Ord v) => t k v -> t' k v

data Interval k v = IA { lower :: Int , upper :: Int }

instance Tree Interval where
  empty = IA 0 0

  insert _ _ (IA lb ub) = IA lb (ub + 1)

  delete _ (IA lb ub) = IA (max 0 (lb - 1)) ub

  merge (IA lb ub) (IA lb' ub') = IA (max lb lb') (ub + ub')

data ListMap k v = LM { list :: [(k, v)] }

instance Tree ListMap where
  empty = LM []

  insert k v (LM []) = LM [(k, v)]
  insert k v (LM ((k', v'):kvs)) | k == k'   = LM $ (k, v):kvs
                                 | otherwise = LM $ (k', v') : list (insert k v (LM kvs))

  delete k lm = LM [ (k', v') | (k', v') <- list lm, k' /= k ]

  merge lm lm' = LM $ list lm ++ [ (k', v') | (k', v') <- list lm' , k' `notElem` map fst (list lm) ]

data KeySet k v = KS { set :: [k] } 

instance Tree KeySet where
  empty = KS []

  insert k v (KS ks) = KS $ nub (k:ks)

  delete k (KS ks) = KS $ [ k' | k' <- ks , k' /= k ]

  merge (KS ks) (KS ks') = KS $ nub (ks ++ ks')

data BST k v = Empty
             | Node k v (BST k v) (BST k v)
             deriving Show

insertCorrect k v Empty = Node k v Empty Empty
insertCorrect k v (Node k' v' tl tr) | k < k'    = Node k' v' (insertCorrect k v tl) tr
                                     | k == k'   = Node k v tl tr
                                     | otherwise = Node k' v' tl (insertCorrect k v tr)

instance (Ord k, Arbitrary k, Arbitrary v) => Arbitrary (BST k v) where
  arbitrary = foldr @[] (uncurry insertCorrect) Empty <$> arbitrary

instance Tree BST where
  empty = Empty

  {- Bug 1 [YES]:
   -    insert k v _ = Node k v Empty Empty
   - This bug is caught by the delete, insert, and merge
   - abstraction properties.
   -}
  insert k v Empty = Node k v Empty Empty
  insert k v (Node k' v' tl tr) | k < k'    = Node k' v' (insert k v tl) tr
                                {- Bug 2 [NO]:
                                 -    comment out the line below
                                 - The abstraction properties do not find this bug.
                                 -}
                                {- Bug 3 [NO]:
                                 -    | k == k'   = Node k' v' tl tr
                                 - The abstraction properties do not find this bug.
                                 -}
                                | k == k'   = Node k' v tl tr
                                {- Bug 5 [YES]:
                                 -    | otherwise = Node k' v' tl (insert k' v tr) 
                                 - The merge abstraction property finds this bug.
                                 -}
                                | otherwise = Node k' v' tl (insert k v tr)

  delete k Empty = Empty
  delete k (Node k' v tl tr) | k == k' = merge tl tr
                             {- Bug 4 [YES]:
                              -     | otherwise = delete k tl
                              - The delete abstraction property finds this bug.
                              -}
                             | otherwise = Node k' v (delete k tl) (delete k tr)

  {- Bug 5 [NO]:
        merge Empty r = r
        merge l Empty = l
        merge (Node k v l r) (Node k' v' l' r') = Node k v l (Node k' v' (merge r l') r')
  - This bug is not caught by the abstraction properties.
  -}
  merge t t' = foldr (uncurry insert) t' $ elements t 
    where
      elements Empty = []
      elements (Node k v tl tr) = elements tl ++ [(k, v)] ++ elements tr

size :: BST k v -> Int
size Empty = 0
size (Node k v tl tr) = 1 + size tl + size tr

instance Abstract Interval BST where
  abstract t = IA (size t) (size t)

instance Specification Interval where
  ia <~ ia' = lower ia' <= lower ia && upper ia <= upper ia'

instance Abstract ListMap BST where
  abstract Empty = LM []
  abstract (Node k v l r) = LM $ (k, v) : list (abstract l) ++ list (abstract r)

instance Specification ListMap where
  lm <~ lm' = sort (list lm) == sort (list lm')

instance Abstract KeySet BST where
  abstract = KS . nub . go
    where
      go Empty = []
      go (Node k v l r) = k : go l ++ go r

instance Specification KeySet where
  ks <~ ks' = sort (set ks) == sort (set ks')

prop_insert_abstract :: Int -> Int -> BST Int Int -> Bool
prop_insert_abstract k v t = abstract @KeySet (insert k v t) <~ insert k v (abstract t)

prop_delete_abstract :: Int -> BST Int Int -> Bool
prop_delete_abstract k t = abstract @KeySet (delete k t) <~ delete k (abstract t)

prop_merge_abstract :: BST Int Int -> BST Int Int -> Bool
prop_merge_abstract t0 t1 = abstract @KeySet (merge t0 t1) <~ merge (abstract t0) (abstract t1)

return []
test = $(quickCheckAll)
