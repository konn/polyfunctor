{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances, GADTs, ImpredicativeTypes          #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses, PolyKinds #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances     #-}
{-# OPTIONS_GHC -fwarn-unused-binds #-}
module Data.Functor.Poly (Polyfunctor', NProd(..)) where
import           Data.Constraint          ((:-) (..))
import           Data.Constraint.Forall   ()
import           Data.Constraint.Forall   (Forall)
import           Data.Constraint.Forall   (inst)
import           Data.Proxy               (Proxy (..))
import           Data.Proxy               (KProxy (..))
import           Data.Type.Equality       ((:~:) (..))
import qualified Data.Type.Equality       as E
import           Data.Type.Natural        (Nat (..), SNat, Sing (SZ, SS), SingI)
import           Data.Type.Natural        (sing, withSingI)
import           Hask.Category            (Bifunctor, Category' (..), Dict (..))
import           Hask.Category            (Dom, Functor (..), NatId, Ob, bimap)
import qualified Hask.Category            as C
import           Hask.Category.Polynomial (Empty, Unit (..))
import           Prelude                  hiding (Functor (..), id, (.))
import           Unsafe.Coerce            (unsafeCoerce)

type family Length ts :: Nat where
  Length '[] = Z
  Length (t ': ts) = S (Length ts)

class (SingI n, Length as ~ n) => NProdOb n as
instance (SingI n, Length as ~ n) => NProdOb n as

type family HighNat (n :: Nat) :: k -> k -> * where
  HighNat (S Z)     = (->)
  HighNat (S (S n)) = C.Nat (->) (HighNat (S n))

class Predfunctor n f (a :: *)
instance Functor f => Predfunctor (S n) f a
instance Polyfunctor' (S n) (f a) => Predfunctor (S (S n)) f a

class (SingI n, Functor f, Dom f ~ (->), Cod f ~ HighNat n, Forall (Predfunctor n f)) => Polyfunctor' (n :: Nat) f
instance (SingI n, Functor f, Dom f ~ (->), Cod f ~ HighNat n, Forall (Predfunctor n f))
         => Polyfunctor' n f

data NProd n xs ys where
  Nullary :: NProd Z '[] '[]
  (:*)    :: (x -> y) -> NProd n xs ys -> NProd (S n) (x ': xs) (y ': ys)

infixr 5 :*

lenZElim :: Z :~: Length xs -> xs :~: '[]
lenZElim Refl = unsafeCoerce (Refl :: () :~: ()) -- Yeah, I know it!

nProdElimL :: NProd n xs ys -> n :~: Length xs
nProdElimL Nullary = Refl
nProdElimL (_ :* fs) =
  case nProdElimL fs of
    Refl -> Refl

nProdElimR :: NProd n xs ys -> n :~: Length ys
nProdElimR Nullary = Refl
nProdElimR (_ :* fs) =
  case nProdElimR fs of
    Refl -> Refl

nProdElimN :: NProd n xs ys -> Length xs :~: Length ys
nProdElimN Nullary = Refl
nProdElimN (_ :* fs) =
  case nProdElimN fs of
    Refl -> Refl

emptyProdL :: NProd Z xs ys -> xs :~: '[]
emptyProdL Nullary = Refl

emptyProdR :: NProd Z xs ys -> ys :~: '[]
emptyProdR Nullary = Refl

class (kparam ~ 'KProxy) => Saturable (kparam :: KProxy k) where
  type Arity' kparam :: Nat
  qArity :: (ToKProxy p ~ kparam) => Q p xs -> Arity p :~: Length xs
  runQ   :: (ToKProxy p ~ kparam) => Q p xs -> (p :$ xs)

instance Saturable ('KProxy :: KProxy *) where
  type Arity' ('KProxy :: KProxy *) = Z
  qArity (QZ _) = Refl
  runQ (QZ p) = p

instance Saturable ('KProxy :: KProxy k) => Saturable ('KProxy :: KProxy (* -> k)) where
  type Arity' ('KProxy :: KProxy (* -> k)) = S (Arity' ('KProxy :: KProxy k))
  qArity (QS q) = case qArity q of Refl -> Refl
  runQ (QS p) = runQ p

class (Saturable kparam) => Polymappable (n :: Nat) (kparam :: KProxy (* -> k)) where
  pmap' :: (ToKProxy (f :: * -> k) ~ kproxy, Polyfunctor' n f)
        => NProd n xs ys -> Q f xs -> Q f ys

instance (Saturable kparam) => Polymappable (S Z) (kparam :: KProxy (* -> *)) where
  pmap' (f :* Nullary) (QS (QZ p)) = QS $ QZ $ C.fmap f p
  pmap' _ _ = error "bug in ghc!"

type FromStar (kparam :: KProxy k) = ('KProxy  :: KProxy (* -> k))

dePredF :: proxy a -> Forall (Predfunctor (S (S n)) f) :- Predfunctor (S (S n)) (f :: * -> k) a
dePredF _ = inst

instance (kparam ~ ('KProxy :: KProxy (* -> k)), Saturable kparam, Polymappable (S n) kparam)
      => Polymappable (S (S n)) (FromStar kparam) where
  pmap' (f :* rs@(_ :* _)) (QS q@(QS _)) = undefined

type ToKProxy (p :: k)  = ('KProxy :: KProxy k)

type Arity (p :: k) = Arity' (ToKProxy p)

type family (p :: k') :$ (xs :: [k]) :: k'' where
  (p :: *) :$ '[] = p
  (p :: * -> k) :$ (x ': xs) = (p x) :$ xs

data family Q (p :: k) (xs :: [*]) :: *
data instance Q (p :: *) xs where
  QZ :: p -> Q p '[]
data instance Q (p :: * -> k) xs where
  QS :: Q (p a) xs -> Q p (a ': xs)

deriving instance Show p     => Show (Q p '[])
deriving instance (Show (Q (p a) xs)) => Show (Q p (a ': xs))

infixr 1 :$

fmap' :: Functor p => proxy p -> Dom p a b -> Cod p (p a) (p b)
fmap' _ = fmap

singletonElim :: NProd n (x ': '[]) (y ': '[]) -> n :~: S Z
singletonElim (f :* Nullary) = Refl

succCons :: NProd (S n) xs ys -> (xs :~: (Head xs ': Tail xs), ys :~: (Head ys ': Tail ys))
succCons (f :* Nullary) = (Refl, Refl)
succCons (f :* np@(_ :* _)) =
  case succCons np of
    (Refl, Refl) -> (Refl, Refl)

highNatOne :: HighNat (S Z) :~: (->)
highNatOne = Refl

type family Snoc (xs :: [k]) (x :: k) where
  Snoc '[]       t = t ': '[]
  Snoc (u ': us) t = u ': Snoc us t

data SnocView (n :: Nat) (xs :: [k]) (ys :: [k]) where
  SnocView :: NProd (S n) xs0 ys0 -> (x -> y) -> SnocView (S (S n)) (Snoc xs0 x) (Snoc ys0 y)

unsnocProd :: NProd (S (S n)) xs ys -> SnocView (S (S n)) xs ys
unsnocProd (f :* g :* Nullary)     = SnocView (f :* Nullary) g
unsnocProd (f :* fs@(_ :* _ :*  _)) =
  case unsnocProd fs of
    SnocView np0 g -> (SnocView (f :* np0) g)
unsnocProd _ = error "bug in GHC!"

{-
pmap :: forall n p xs ys proxy. Polyfunctor' n p => proxy p -> NProd n xs ys -> Q p xs -> Q p ys
pmap _ Nullary p             = p
pmap pxy pr@(f :* Nullary) (QS (QZ p)) = undefined -- fmap' pxy f q
pmap _ (f :* fs@(_ :* _))  p = undefined --C.fmap f q
-}
type family Head (ts :: [*]) where
  Head (t ': xs) = t

type family Tail (ts :: [*]) where
  Tail (t ': ts) = ts

type family Last ts where
  Last (t ': '[]) = t
  Last (t ': ts)  = Last ts

type family Init xs where
  Init (t ': '[]) = '[]
  Init (t ': ts) = t ': Init ts

data Triad a b c = First a | Second b | Third c
                 deriving (Read, Show, Eq, Ord)

instance Functor (Triad c d) where
  type Dom (Triad c d) = (->)
  type Cod (Triad c d) = (->)
  fmap _ (First  c) = First  c
  fmap _ (Second d) = Second d
  fmap f (Third  a) = Third  (f a)

instance Functor (Triad a) where
  type Dom (Triad a) = (->)
  type Cod (Triad a) = C.Nat (->) (->)
  fmap f0 = C.Nat $ go f0
    where
      go :: (u -> v) -> Triad d u c -> Triad d v c
      go _ (First  d) = First  d
      go f (Second a) = Second (f a)
      go _ (Third  c) = Third c

instance Functor Triad where
  type Dom Triad = (->)
  type Cod Triad = C.Nat (->) (C.Nat (->) (->))
  fmap f0 = C.Nat (C.Nat $ go f0)
    where
      go :: (a -> b) -> Triad a c d -> Triad b c d
      go f (First  a) = First  (f a)
      go _ (Second c) = Second c
      go _ (Third  d) = Third  d


