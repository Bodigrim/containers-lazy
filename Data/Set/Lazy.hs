-- |
-- Module      :  Data.Set.Lazy
-- Copyright   :  (c) Andrew Lelechenko 2019, Daan Leijen 2002
-- License     :  BSD3
-- Maintainer  :  andrew.lelechenko@gmail.com
--
--
-- = Possibly infinite Sets
--
-- The @'Set' e@ type represents a lazy set of elements of type @e@.
-- Most operations require that @e@ be an instance of the 'Ord' class.
--
-- This module is a drop-in replacement for 'Data.Set'
-- and implements the same API.
-- It is intended to be imported qualified, to avoid name
-- clashes with Prelude functions, e.g.
--
-- >  import Data.Set.Lazy (Set)
-- >  import qualified Data.Set.Lazy as Set

{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE RoleAnnotations            #-}
{-# LANGUAGE TypeFamilies               #-}

module Data.Set.Lazy (
  -- * Set type
    Set
  -- * Construction
  , empty
  , singleton
  , fromList
  , fromAscList
  , fromDescList
  , fromDistinctAscList
  , fromDistinctDescList
  , powerSet

  -- * Insertion
  , insert

  -- * Deletion
  , delete

  -- * Query
  , member
  , notMember
  , lookupLT
  , lookupGT
  , lookupLE
  , lookupGE
  , null
  , size
  , isSubsetOf
  , isProperSubsetOf
  , disjoint

  -- * Combine
  , union
  , unions
  , difference
  , (\\)
  , intersection
  , cartesianProduct
  , disjointUnion

  -- * Filter
  , filter
  , takeWhileAntitone
  , dropWhileAntitone
  , spanAntitone
  , partition
  , split
  , splitMember

  -- * Indexed
  , lookupIndex
  , findIndex
  , elemAt
  , deleteAt
  , take
  , drop
  , splitAt

  -- * Map
  , map
  , mapMonotonic

  -- * Min\/Max
  , lookupMin
  , lookupMax
  , findMin
  , findMax
  , deleteMin
  , deleteMax
  , deleteFindMin
  , deleteFindMax
  , maxView
  , minView

  -- * Conversion

  -- ** List
  , elems
  , toList
  , toAscList
  , toDescList
  ) where


import Prelude hiding (filter,foldl,foldr,null,map,take,drop,splitAt)
import qualified Data.List as List
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid (Monoid(..))
#endif
#if MIN_VERSION_base(4,9,0)
import Data.Semigroup (Semigroup((<>), stimes), stimesIdempotentMonoid)
import Data.Functor.Classes
#endif
import qualified Data.Foldable as Foldable
#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable (foldMap))
#endif
import Data.Typeable
import Control.DeepSeq (NFData())

#if __GLASGOW_HASKELL__
#if __GLASGOW_HASKELL__ >= 708
import qualified GHC.Exts as GHCExts
#endif
import Text.Read ( readPrec, Read (..), Lexeme (..), parens, prec
                 , lexP, readListPrecDefault )
import Data.Data
#endif


{--------------------------------------------------------------------
  Operators
--------------------------------------------------------------------}
infixl 9 \\ --

-- | /O(n+m)/. See 'difference'.
(\\) :: Ord a => Set a -> Set a -> Set a
m1 \\ m2 = difference m1 m2
#if __GLASGOW_HASKELL__
{-# INLINABLE (\\) #-}
#endif

-- | A set of values @a@.
newtype Set a = Set [a]
  deriving (Eq, Ord, Foldable, Data, Typeable, NFData)

#if __GLASGOW_HASKELL__ >= 708
type role Set nominal
#endif

instance Ord a => Monoid (Set a) where
    mempty  = empty
    mconcat = unions
#if !(MIN_VERSION_base(4,9,0))
    mappend = union
#else
    mappend = (<>)

instance Ord a => Semigroup (Set a) where
    (<>)    = union
    stimes  = stimesIdempotentMonoid
#endif

{--------------------------------------------------------------------
  Query
--------------------------------------------------------------------}
-- | /O(1)/. Is this the empty set?
null :: Set a -> Bool
null (Set xs) = List.null xs
{-# INLINE null #-}

-- | /O(n)/. The number of elements in the set.
size :: Set a -> Int
size (Set xs) = List.length xs
{-# INLINE size #-}

-- | /O(n)/. Is the element in the set?
member :: Ord a => a -> Set a -> Bool
member x (Set xs) = go xs
  where
    go = \case
      [] -> False
      y : ys -> case x `compare` y of
        LT -> False
        EQ -> True
        GT -> go ys
#if __GLASGOW_HASKELL__
{-# INLINABLE member #-}
#else
{-# INLINE member #-}
#endif

-- | /O(n)/. Is the element not in the set?
notMember :: Ord a => a -> Set a -> Bool
notMember a t = not $ member a t
#if __GLASGOW_HASKELL__
{-# INLINABLE notMember #-}
#else
{-# INLINE notMember #-}
#endif

-- | /O(n)/. Find largest element smaller than the given one.
--
-- > lookupLT 3 (fromList [3, 5]) == Nothing
-- > lookupLT 5 (fromList [3, 5]) == Just 3
lookupLT :: Ord a => a -> Set a -> Maybe a
lookupLT x (Set xs) = goNothing xs
  where
    goNothing [] = Nothing
    goNothing (y : ys)
      | y < x     = goJust y ys
      | otherwise = Nothing

    goJust acc [] = Just acc
    goJust acc (y : ys)
      | y < x     = goJust y ys
      | otherwise = Just acc

#if __GLASGOW_HASKELL__
{-# INLINABLE lookupLT #-}
#else
{-# INLINE lookupLT #-}
#endif

-- | /O(n)/. Find smallest element greater than the given one.
--
-- > lookupGT 4 (fromList [3, 5]) == Just 5
-- > lookupGT 5 (fromList [3, 5]) == Nothing
lookupGT :: Ord a => a -> Set a -> Maybe a
lookupGT x (Set xs) = case List.dropWhile (<= x) xs of
  []    -> Nothing
  y : _ -> Just y
#if __GLASGOW_HASKELL__
{-# INLINABLE lookupGT #-}
#else
{-# INLINE lookupGT #-}
#endif

-- | /O(n)/. Find largest element smaller or equal to the given one.
--
-- > lookupLE 2 (fromList [3, 5]) == Nothing
-- > lookupLE 4 (fromList [3, 5]) == Just 3
-- > lookupLE 5 (fromList [3, 5]) == Just 5
lookupLE :: Ord a => a -> Set a -> Maybe a
lookupLE x (Set xs) = goNothing xs
  where
    goNothing [] = Nothing
    goNothing (y : ys)
      | y <= x    = goJust y ys
      | otherwise = Nothing

    goJust acc [] = Just acc
    goJust acc (y : ys)
      | y <= x    = goJust y ys
      | otherwise = Just acc
#if __GLASGOW_HASKELL__
{-# INLINABLE lookupLE #-}
#else
{-# INLINE lookupLE #-}
#endif

-- | /O(n)/. Find smallest element greater or equal to the given one.
--
-- > lookupGE 3 (fromList [3, 5]) == Just 3
-- > lookupGE 4 (fromList [3, 5]) == Just 5
-- > lookupGE 6 (fromList [3, 5]) == Nothing
lookupGE :: Ord a => a -> Set a -> Maybe a
lookupGE x (Set xs) = case List.dropWhile (< x) xs of
  []    -> Nothing
  y : _ -> Just y
#if __GLASGOW_HASKELL__
{-# INLINABLE lookupGE #-}
#else
{-# INLINE lookupGE #-}
#endif

{--------------------------------------------------------------------
  Construction
--------------------------------------------------------------------}
-- | /O(1)/. The empty set.
empty  :: Set a
empty = Set []
{-# INLINE empty #-}

-- | /O(1)/. Create a singleton set.
singleton :: a -> Set a
singleton x = Set [x]
{-# INLINE singleton #-}

{--------------------------------------------------------------------
  Insertion, Deletion
--------------------------------------------------------------------}
-- | /O(n)/. Insert an element in a set.
-- If the set already contains an element equal to the given value,
-- it is replaced with the new value.
insert :: Ord a => a -> Set a -> Set a
insert x (Set xs) = Set (go xs)
  where
    go zs = case zs of
      []     -> [x]
      y : ys -> case x `compare` y of
        LT -> x : zs
        EQ -> x : ys
        GT -> y : go ys
#if __GLASGOW_HASKELL__
{-# INLINABLE insert #-}
#else
{-# INLINE insert #-}
#endif

#ifndef __GLASGOW_HASKELL__
lazy :: a -> a
lazy a = a
#endif

-- | /O(n)/. Delete an element from a set.
delete :: Ord a => a -> Set a -> Set a
delete x (Set xs) = Set (go xs)
  where
    go zs = case zs of
      []     -> []
      y : ys -> case x `compare` y of
        LT -> zs
        EQ -> ys
        GT -> y : go ys
#if __GLASGOW_HASKELL__
{-# INLINABLE delete #-}
#else
{-# INLINE delete #-}
#endif

{--------------------------------------------------------------------
  Subset
--------------------------------------------------------------------}
-- | /O(n+m)/. Is this a proper subset? (ie. a subset but not equal).
isProperSubsetOf :: Ord a => Set a -> Set a -> Bool
isProperSubsetOf (Set xs) (Set ys) = go xs ys
  where
    go [] [] = False
    go [] _  = True
    go _  [] = False
    go vvs@(v : vs) (w : ws) = case v `compare` w of
      LT -> False
      EQ -> go vs ws
      GT -> isSubsetOf (Set vvs) (Set ws)
#if __GLASGOW_HASKELL__
{-# INLINABLE isProperSubsetOf #-}
#endif


-- | /O(n+m)/. Is this a subset?
-- @(s1 \`isSubsetOf\` s2)@ tells whether @s1@ is a subset of @s2@.
isSubsetOf :: Ord a => Set a -> Set a -> Bool
isSubsetOf (Set xs) (Set ys) = go xs ys
  where
    go [] _  = True
    go _  [] = False
    go vvs@(v : vs) (w : ws) = case v `compare` w of
      LT -> False
      EQ -> go vs ws
      GT -> go vvs ws
#if __GLASGOW_HASKELL__
{-# INLINABLE isSubsetOf #-}
#endif

{--------------------------------------------------------------------
  Disjoint
--------------------------------------------------------------------}
-- | /O(n+m)/. Check whether two sets are disjoint (i.e. their intersection
--   is empty).
--
-- > disjoint (fromList [2,4,6])   (fromList [1,3])     == True
-- > disjoint (fromList [2,4,6,8]) (fromList [2,3,5,7]) == False
-- > disjoint (fromList [1,2])     (fromList [1,2,3,4]) == False
-- > disjoint (fromList [])        (fromList [])        == True

disjoint :: Ord a => Set a -> Set a -> Bool
disjoint (Set xs) (Set ys) = go xs ys
  where
    go [] _ = True
    go _ [] = True
    go vvs@(v : vs) wws@(w : ws) = case v `compare` w of
      LT -> go vs wws
      EQ -> False
      GT -> go vvs ws

{--------------------------------------------------------------------
  Minimal, Maximal
--------------------------------------------------------------------}

-- | /O(1)/. The minimal element of a set.
lookupMin :: Set a -> Maybe a
lookupMin (Set xs) = case xs of
  []    -> Nothing
  x : _ -> Just x

-- | /O(1)/. The minimal element of a set.
findMin :: Set a -> a
findMin (Set xs) = List.head xs

-- | /O(n)/. The maximal element of a set.
lookupMax :: Set a -> Maybe a
lookupMax (Set xs) = case xs of
  [] -> Nothing
  _  -> Just (List.last xs)

-- | /O(n)/. The maximal element of a set.
findMax :: Set a -> a
findMax (Set xs) = List.last xs

-- | /O(1)/. Delete the minimal element. Returns an empty set if the set is empty.
deleteMin :: Set a -> Set a
deleteMin (Set xs) = Set (List.tail xs)

-- | /O(n)/. Delete the maximal element. Returns an empty set if the set is empty.
deleteMax :: Set a -> Set a
deleteMax (Set xs) = Set (List.init xs)

{--------------------------------------------------------------------
  Union.
--------------------------------------------------------------------}
-- | The union of a list of sets: (@'unions' == 'foldl' 'union' 'empty'@).
unions :: (Foldable f, Ord a) => f (Set a) -> Set a
unions = Foldable.foldl' union empty
#if __GLASGOW_HASKELL__
{-# INLINABLE unions #-}
#endif

-- | /O(n+m)/. The union of two sets, preferring the first set when
-- equal elements are encountered.
union :: Ord a => Set a -> Set a -> Set a
union = mergeWith compare id (\x _ -> Just x) id
#if __GLASGOW_HASKELL__
{-# INLINABLE union #-}
#endif

{--------------------------------------------------------------------
  Difference
--------------------------------------------------------------------}
-- | /O(n+m)/. Difference of two sets.
difference :: Ord a => Set a -> Set a -> Set a
difference = mergeWith compare id (\_ _ -> Nothing) (\_ -> [])
#if __GLASGOW_HASKELL__
{-# INLINABLE difference #-}
#endif

{--------------------------------------------------------------------
  Intersection
--------------------------------------------------------------------}
-- | /O(n+m)/. The intersection of two sets.
-- Elements of the result come from the first set, so for example
--
-- > import qualified Data.Set as S
-- > data AB = A | B deriving Show
-- > instance Ord AB where compare _ _ = EQ
-- > instance Eq AB where _ == _ = True
-- > main = print (S.singleton A `S.intersection` S.singleton B,
-- >               S.singleton B `S.intersection` S.singleton A)
--
-- prints @(fromList [A],fromList [B])@.
intersection :: Ord a => Set a -> Set a -> Set a
intersection = mergeWith compare (\_ -> []) (\x _ -> Just x) (\_ -> [])
#if __GLASGOW_HASKELL__
{-# INLINABLE intersection #-}
#endif

mergeWith
  :: (a -> b -> Ordering)
  -> ([a] -> [c])
  -> (a -> b -> Maybe c)
  -> ([b] -> [c])
  -> Set a
  -> Set b
  -> Set c
mergeWith cmpr lt eq gt (Set as) (Set bs) = Set (go as bs)
  where
    go xs [] = lt xs
    go [] ys = gt ys
    go xs@(x : xs') ys@(y : ys') = case x `cmpr` y of
      LT -> lt [x] ++ go xs' ys
      EQ -> maybe id (:) (eq x y) (go xs' ys')
      GT -> gt [y] ++ go xs ys'
{-# INLINE mergeWith #-}

{--------------------------------------------------------------------
  Filter and partition
--------------------------------------------------------------------}
-- | /O(n)/. Filter all elements that satisfy the predicate.
filter :: (a -> Bool) -> Set a -> Set a
filter f (Set xs) = Set (List.filter f xs)

-- | /O(n)/. Partition the set into two sets, one with all elements that satisfy
-- the predicate and one with all elements that don't satisfy the predicate.
-- See also 'split'.
partition :: (a -> Bool) -> Set a -> (Set a, Set a)
partition f (Set xs) = (Set ys, Set zs)
  where
    (ys, zs) = List.partition f xs

{----------------------------------------------------------------------
  Map
----------------------------------------------------------------------}

-- | /O(n*log n)/.
-- @'map' f s@ is the set obtained by applying @f@ to each element of @s@.
--
-- It's worth noting that the size of the result may be smaller if,
-- for some @(x,y)@, @x \/= y && f x == f y@

map :: Ord b => (a -> b) -> Set a -> Set b
map f = fromList . List.map f . toList
#if __GLASGOW_HASKELL__
{-# INLINABLE map #-}
#endif

-- | /O(n)/. The
--
-- @'mapMonotonic' f s == 'map' f s@, but works only when @f@ is strictly increasing.
-- /The precondition is not checked./
-- Semi-formally, we have:
--
-- > and [x < y ==> f x < f y | x <- ls, y <- ls]
-- >                     ==> mapMonotonic f s == map f s
-- >     where ls = toList s

mapMonotonic :: (a -> b) -> Set a -> Set b
mapMonotonic f (Set xs) = Set (List.map f xs)

{--------------------------------------------------------------------
  List variations
--------------------------------------------------------------------}
-- | /O(n)/. An alias of 'toAscList'. The elements of a set in ascending order.
elems :: Set a -> [a]
elems = toAscList

{--------------------------------------------------------------------
  Lists
--------------------------------------------------------------------}
#if __GLASGOW_HASKELL__ >= 708
instance (Ord a) => GHCExts.IsList (Set a) where
  type Item (Set a) = a
  fromList = fromList
  toList   = toList
#endif

-- | /O(n)/. Convert the set to a list of elements.
toList :: Set a -> [a]
toList (Set xs) = xs

-- | /O(n)/. Convert the set to an ascending list of elements.
toAscList :: Set a -> [a]
toAscList (Set xs) = xs

-- | /O(n)/. Convert the set to a descending list of elements.
toDescList :: Set a -> [a]
toDescList (Set xs) = reverse xs

-- | /O(n*log n)/. Create a set from a list of elements.
fromList :: Ord a => [a] -> Set a
fromList = Set . combineEq . List.sort
#if __GLASGOW_HASKELL__
{-# INLINABLE fromList #-}
#endif

-- | /O(n)/. Build a set from an ascending list in linear time.
-- /The precondition (input list is ascending) is not checked./
fromAscList :: Eq a => [a] -> Set a
fromAscList xs = fromDistinctAscList (combineEq xs)
#if __GLASGOW_HASKELL__
{-# INLINABLE fromAscList #-}
#endif

-- | /O(n)/. Build a set from a descending list in linear time.
-- /The precondition (input list is descending) is not checked./
fromDescList :: Eq a => [a] -> Set a
fromDescList xs = fromDistinctDescList (combineEq xs)
#if __GLASGOW_HASKELL__
{-# INLINABLE fromDescList #-}
#endif

combineEq :: Eq a => [a] -> [a]
combineEq [] = []
combineEq (x : xs) = combineEq' x xs
  where
    combineEq' z [] = [z]
    combineEq' z (y:ys)
      | z == y = combineEq' z ys
      | otherwise = z : combineEq' y ys

-- | /O(n)/. Build a set from an ascending list of distinct elements in linear time.
-- /The precondition (input list is strictly ascending) is not checked./
fromDistinctAscList :: [a] -> Set a
fromDistinctAscList = Set

-- | /O(n)/. Build a set from a descending list of distinct elements in linear time.
-- /The precondition (input list is strictly descending) is not checked./
fromDistinctDescList :: [a] -> Set a
fromDistinctDescList = Set . reverse

{--------------------------------------------------------------------
  Show
--------------------------------------------------------------------}
instance Show a => Show (Set a) where
  showsPrec p xs = showParen (p > 10) $
    showString "fromList " . shows (toList xs)

#if MIN_VERSION_base(4,9,0)
instance Eq1 Set where
    liftEq eq m n =
        size m == size n && liftEq eq (toList m) (toList n)

instance Ord1 Set where
    liftCompare cmp m n =
        liftCompare cmp (toList m) (toList n)

instance Show1 Set where
    liftShowsPrec sp sl d m =
        showsUnaryWith (liftShowsPrec sp sl) "fromList" d (toList m)
#endif

{--------------------------------------------------------------------
  Read
--------------------------------------------------------------------}
instance (Read a, Ord a) => Read (Set a) where
#ifdef __GLASGOW_HASKELL__
  readPrec = parens $ prec 10 $ do
    Ident "fromList" <- lexP
    xs <- readPrec
    return (fromList xs)

  readListPrec = readListPrecDefault
#else
  readsPrec p = readParen (p > 10) $ \ r -> do
    ("fromList",s) <- lex r
    (xs,t) <- reads s
    return (fromList xs,t)
#endif

{--------------------------------------------------------------------
  Split
--------------------------------------------------------------------}
-- | /O(n)/. The expression (@'split' x set@) is a pair @(set1,set2)@
-- where @set1@ comprises the elements of @set@ less than @x@ and @set2@
-- comprises the elements of @set@ greater than @x@.
split :: Ord a => a -> Set a -> (Set a, Set a)
split x (Set xs) = (Set ys, Set vs)
  where
    (ys, zs) = List.span (< x) xs
    vs = case zs of
      w : ws
        | w == x -> ws
      _ -> zs
{-# INLINABLE split #-}

-- | /O(n)/. Performs a 'split' but also returns whether the pivot
-- element was found in the original set.
splitMember :: Ord a => a -> Set a -> (Set a, Bool, Set a)
splitMember x (Set xs) = (Set ys, b, Set vs)
  where
    (ys, zs) = List.span (< x) xs
    (b, vs) = case zs of
      w : ws
        | w == x -> (True, ws)
      _ -> (False, zs)
#if __GLASGOW_HASKELL__
{-# INLINABLE splitMember #-}
#endif

{--------------------------------------------------------------------
  Indexing
--------------------------------------------------------------------}

-- | /O(n)/. Return the /index/ of an element, which is its zero-based
-- index in the sorted sequence of elements. The index is a number from /0/ up
-- to, but not including, the 'size' of the set. Calls 'error' when the element
-- is not a 'member' of the set.
--
-- > findIndex 2 (fromList [5,3])    Error: element is not in the set
-- > findIndex 3 (fromList [5,3]) == 0
-- > findIndex 5 (fromList [5,3]) == 1
-- > findIndex 6 (fromList [5,3])    Error: element is not in the set
findIndex :: Ord a => a -> Set a -> Int
findIndex x (Set xs) = go 0 xs
  where
    go _ [] = error "element is not in the set"
    go n (y : ys) = case x `compare` y of
      LT -> error "element is not in the set"
      EQ -> n
      GT -> go (n + 1) ys
#if __GLASGOW_HASKELL__
{-# INLINABLE findIndex #-}
#endif

-- | /O(n)/. Lookup the /index/ of an element, which is its zero-based index in
-- the sorted sequence of elements. The index is a number from /0/ up to, but not
-- including, the 'size' of the set.
--
-- > isJust   (lookupIndex 2 (fromList [5,3])) == False
-- > fromJust (lookupIndex 3 (fromList [5,3])) == 0
-- > fromJust (lookupIndex 5 (fromList [5,3])) == 1
-- > isJust   (lookupIndex 6 (fromList [5,3])) == False
lookupIndex :: Ord a => a -> Set a -> Maybe Int
lookupIndex x (Set xs) = go 0 xs
  where
    go _ [] = Nothing
    go n (y : ys) = case x `compare` y of
      LT -> Nothing
      EQ -> Just n
      GT -> go (n + 1) ys
#if __GLASGOW_HASKELL__
{-# INLINABLE lookupIndex #-}
#endif

-- | /O(n)/. Retrieve an element by its /index/, i.e. by its zero-based
-- index in the sorted sequence of elements. If the /index/ is out of range (less
-- than zero, greater or equal to 'size' of the set), 'error' is called.
--
-- > elemAt 0 (fromList [5,3]) == 3
-- > elemAt 1 (fromList [5,3]) == 5
-- > elemAt 2 (fromList [5,3])    Error: index out of range

elemAt :: Int -> Set a -> a
elemAt n (Set xs) = xs List.!! n

-- | /O(n)/. Delete the element at /index/, i.e. by its zero-based index in
-- the sorted sequence of elements. If the /index/ is out of range (less than zero,
-- greater or equal to 'size' of the set), 'error' is called.
--
-- > deleteAt 0    (fromList [5,3]) == singleton 5
-- > deleteAt 1    (fromList [5,3]) == singleton 3
-- > deleteAt 2    (fromList [5,3])    Error: index out of range
-- > deleteAt (-1) (fromList [5,3])    Error: index out of range

deleteAt :: Int -> Set a -> Set a
deleteAt n (Set xs)
  | n < 0     = error "index out of range"
  | otherwise = case List.splitAt n xs of
    (_, [])      -> error "index out of range"
    (ys, _ : zs) -> Set (ys <> zs)

-- | Take a given number of elements in order, beginning
-- with the smallest ones.
--
-- @
-- take n = 'fromDistinctAscList' . 'Prelude.take' n . 'toAscList'
-- @
take :: Int -> Set a -> Set a
take n (Set xs) = Set (List.take n xs)

-- | Drop a given number of elements in order, beginning
-- with the smallest ones.
--
-- @
-- drop n = 'fromDistinctAscList' . 'Prelude.drop' n . 'toAscList'
-- @
drop :: Int -> Set a -> Set a
drop n (Set xs) = Set (List.drop n xs)

-- | /O(n)/. Split a set at a particular index.
--
-- @
-- splitAt !n !xs = ('take' n xs, 'drop' n xs)
-- @
splitAt :: Int -> Set a -> (Set a, Set a)
splitAt n (Set xs) = (Set ys, Set zs)
  where
    (ys, zs) = List.splitAt n xs

-- | /O(n)/. Take while a predicate on the elements holds.
-- The user is responsible for ensuring that for all elements @j@ and @k@ in the set,
-- @j \< k ==\> p j \>= p k@. See note at 'spanAntitone'.
--
-- @
-- takeWhileAntitone p = 'fromDistinctAscList' . 'Data.List.takeWhile' p . 'toList'
-- takeWhileAntitone p = 'filter' p
-- @

takeWhileAntitone :: (a -> Bool) -> Set a -> Set a
takeWhileAntitone f (Set xs) = Set (List.takeWhile f xs)

-- | /O(n)/. Drop while a predicate on the elements holds.
-- The user is responsible for ensuring that for all elements @j@ and @k@ in the set,
-- @j \< k ==\> p j \>= p k@. See note at 'spanAntitone'.
--
-- @
-- dropWhileAntitone p = 'fromDistinctAscList' . 'Data.List.dropWhile' p . 'toList'
-- dropWhileAntitone p = 'filter' (not . p)
-- @

dropWhileAntitone :: (a -> Bool) -> Set a -> Set a
dropWhileAntitone f (Set xs) = Set (List.dropWhile f xs)

-- | /O(n)/. Divide a set at the point where a predicate on the elements stops holding.
-- The user is responsible for ensuring that for all elements @j@ and @k@ in the set,
-- @j \< k ==\> p j \>= p k@.
--
-- @
-- spanAntitone p xs = ('takeWhileAntitone' p xs, 'dropWhileAntitone' p xs)
-- spanAntitone p xs = partition p xs
-- @
--
-- Note: if @p@ is not actually antitone, then @spanAntitone@ will split the set
-- at some /unspecified/ point where the predicate switches from holding to not
-- holding (where the predicate is seen to hold before the first element and to fail
-- after the last element).

spanAntitone :: (a -> Bool) -> Set a -> (Set a, Set a)
spanAntitone f (Set xs) = (Set ys, Set zs)
  where
    (ys, zs) = List.partition f xs

-- | /O(1)/. Delete and find the minimal element.
--
-- > deleteFindMin set = (findMin set, deleteMin set)

deleteFindMin :: Set a -> (a, Set a)
deleteFindMin (Set xs) = case xs of
  []     -> error "deleteFindMin: empty set"
  y : ys -> (y, Set ys)

-- | /O(n)/. Delete and find the maximal element.
--
-- > deleteFindMax set = (findMax set, deleteMax set)
deleteFindMax :: Set a -> (a, Set a)
deleteFindMax (Set xs) = case xs of
  [] -> error "deleteFindMax: empty set"
  y : ys -> let (z, zs) = go y ys in (z, Set zs)
  where
    go t [] = (t, [])
    go t (v : vs) = let (z, zs) = go v vs in (z, t : zs)

-- | /O(1)/. Retrieves the minimal key of the set, and the set
-- stripped of that element, or 'Nothing' if passed an empty set.
minView :: Set a -> Maybe (a, Set a)
minView (Set xs) = case xs of
  []     -> Nothing
  y : ys -> Just (y, Set ys)

-- | /O(n)/. Retrieves the maximal key of the set, and the set
-- stripped of that element, or 'Nothing' if passed an empty set.
maxView :: Set a -> Maybe (a, Set a)
maxView (Set xs) = case xs of
  [] -> Nothing
  y : ys -> let (z, zs) = go y ys in Just (z, Set zs)
  where
    go t [] = (t, [])
    go t (v : vs) = let (z, zs) = go v vs in (z, t : zs)

{--------------------------------------------------------------------
  Utilities
--------------------------------------------------------------------}

-- | Calculate the power set of a set: the set of all its subsets.
--
-- @
-- t ``member`` powerSet s == t ``isSubsetOf`` s
-- @
--
-- Example:
--
-- @
-- powerSet (fromList [1,2,3]) =
--   fromList [[], [1], [2], [3], [1,2], [1,3], [2,3], [1,2,3]]
-- @
powerSet :: Set a -> Set (Set a)
powerSet (Set xs) = Set (Set [] : List.map Set (go xs))
  where
    go [] = []
    go (y : ys) = [y] : List.map (y :) yys ++ yys
      where
        yys = go ys

-- | Calculate the Cartesian product of two sets.
--
-- @
-- cartesianProduct xs ys = fromList $ liftA2 (,) (toList xs) (toList ys)
-- @
--
-- Example:
--
-- @
-- cartesianProduct (fromList [1,2]) (fromList ['a','b']) =
--   fromList [(1,'a'), (1,'b'), (2,'a'), (2,'b')]
-- @
cartesianProduct :: Set a -> Set b -> Set (a, b)
cartesianProduct (Set as) (Set bs) = Set [ (a, b) | a <- as, b <- bs]

-- | Calculate the disjoint union of two sets.
--
-- @ disjointUnion xs ys = map Left xs ``union`` map Right ys @
--
-- Example:
--
-- @
-- disjointUnion (fromList [1,2]) (fromList ["hi", "bye"]) =
--   fromList [Left 1, Left 2, Right "hi", Right "bye"]
-- @
disjointUnion :: Set a -> Set b -> Set (Either a b)
disjointUnion (Set as) (Set bs) = Set (List.map Left as <> List.map Right bs)
