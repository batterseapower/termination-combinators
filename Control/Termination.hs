{-# LANGUAGE ExistentialQuantification, RankNTypes #-}
module Control.Termination (
    TestResult(..), test,
    TTest, initHistory,

    alwaysT,
    Finite(..), finiteT, boolT, unitT,
    WellOrdered(..), intT,
    eitherT, pairT,
    finiteMapT,
    Fix(..), fixT, gfixT,
  ) where

import Control.Applicative
import Control.Arrow ((***))

import Data.Functor.Contravariant
import Data.Map (Map)
import qualified Data.Map as M
import Data.Traversable (Traversable(..))

import Unsafe.Coerce


data TestResult a = Stop
                  | Continue (History a)

data History a = H { test :: a -> TestResult a }

data TTest a = forall b. WQO (a -> b) (b -> b -> Bool)

etaTTest :: TTest a -> TTest a
etaTTest tt = WQO (case tt of WQO f _ -> unsafeCoerce f) (case tt of WQO _ t -> unsafeCoerce t)

initHistory :: TTest a -> History a
initHistory (WQO f (<|)) = H $ go []
  where
    go ys x
      | any (<| y) ys = Stop
      | otherwise     = Continue $ H $ go (y:ys)
      where y = f x


alwaysT :: TTest a
alwaysT = WQO id (\_ _ -> True)


class Eq a => Finite a where

finiteT :: Finite a => TTest a
finiteT = WQO id (==)

instance Finite ()
instance Finite Bool
instance Finite a => Finite (Maybe a)
instance (Finite a, Finite b) => Finite (a, b)
instance (Finite a, Finite b) => Finite (Either a b)

boolT :: TTest Bool
boolT = finiteT

unitT :: TTest ()
unitT = finiteT


class Ord a => WellOrdered a where

wellOrderedT :: WellOrdered a => TTest a
wellOrderedT = WQO id (<=)

instance WellOrdered Int where

intT :: TTest Int
intT = wellOrderedT


instance Contravariant TTest where
    contramap g (WQO f (<|)) = WQO (f . g) (<|)


eitherT :: TTest a -> TTest b -> TTest (Either a b)
eitherT (WQO fa ta) (WQO fb tb) = WQO (either (Left . fa) (Right . fb)) t
  where t (Left a1)  (Left a2)  = a1 `ta` a2
        t (Right b1) (Right b2) = b1 `tb` b2
        t _          _          = False

pairT :: TTest a -> TTest b -> TTest (a, b)
pairT (WQO fa ta) (WQO fb tb) = WQO (fa *** fb) t
  where t (a1, b1) (a2, b2) = a1 `ta` a2 && b1 `tb` b2


finiteMapT :: (Ord k, Finite k) => TTest v -> TTest (Map k v)
finiteMapT (WQO fv tv) = WQO (M.map fv) t
  where t m1 m2 = M.keysSet m1 == M.keysSet m2 &&
                  all (ok m1) (M.assocs m2)
        ok m1 (k2, v2) = case M.lookup k2 m1 of
            Just v1 -> v1 `tv` v2
            Nothing -> error "finiteMapT"


newtype Fix f = Roll { unroll :: f (Fix f) }

-- Used to memoise per-element work of datatype fixed points
data FixMem b = RollMem { memIt :: b, memKids :: [FixMem b] }

fixT :: Functor t
     => (forall rec. t rec -> [rec])
     -> (forall rec. t rec -> t rec)
     -> (forall rec. TTest rec -> TTest (t rec))
     -> TTest (Fix t)
fixT kids p f = wqo
  where
    wqo = case f (etaTTest wqo) of
            WQO inj (<|) -> WQO inj_fix test
              where
                test a b = (<|) (memIt a) (memIt b) ||
                           any (test a) (memKids b)
                
                inj_fix (Roll t) = RollMem { memIt = inj (p t),
                                             memKids = map inj_fix (kids t) }


gfixT :: Traversable t
      => (forall rec. TTest rec -> TTest (t rec))
      -> TTest (Fix t)
gfixT = fixT kids_traverse id

newtype Gather a b = Gather { unGather :: [a] -> [a] }
 -- Difference lists: why not?

runGather :: Gather a b -> [a]
runGather = ($ []) . unGather

instance Functor (Gather a) where
    fmap _ (Gather xs) = Gather xs

instance Applicative (Gather a) where
    pure _ = Gather id
    Gather xs <*> Gather ys = Gather (xs . ys)

kids_traverse :: Traversable t => t a -> [a]
kids_traverse = runGather . traverse (\x -> Gather (x:))
