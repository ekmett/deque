{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -Wall #-}

module Data.Deque.Cat where

import Control.DeepSeq
import Data.Type.Bool
import qualified Data.Deque.NonCat as NC
import qualified Data.Sequence as Seq
import Data.List

type T = True
type F = False

data Buffer q i j where
  B1 :: !(q i j) -> Buffer q i j
  B2 :: !(q j k) -> !(q i j) -> Buffer q i k
  B3 :: !(q k l) -> !(q j k) -> !(q i j) -> Buffer q i l
  B4 :: !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> Buffer q i m
  B5 :: !(q m n) -> !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> Buffer q i n
  B6 :: !(q n o) -> !(q m n) -> !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> Buffer q i o
  B7 :: !(q o p) -> !(q n o) -> !(q m n) -> !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> Buffer q i p
  B8 :: !(q p r) -> !(q o p) -> !(q n o) -> !(q m n) -> !(q l m) -> !(q k l) -> !(q j k) -> !(q i j)  -> Buffer q i r
  B9 :: !(NC.Deque q s t) -> !(q r s) -> !(q p r) -> !(q o p) -> !(q n o) -> !(q m n) -> !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> !(NC.Deque q h i) -> Buffer q h t

instance NFData (Buffer q i j) where
  rnf !_ = ()

instance Show (Buffer q i j) where
  show B1{} = "B1"
  show B2{} = "B2"
  show B3{} = "B3"
  show B4{} = "B4"
  show B5{} = "B5"
  show B6{} = "B6"
  show B7{} = "B7"
  show B8{} = "B8"
  show B9{} = "B9"

pushB :: q j k -> Buffer q i j -> Buffer q i k
pushB a (B1 b)                         = B2 a b
pushB a (B2 b c)                       = B3 a b c
pushB a (B3 b c d)                     = B4 a b c d
pushB a (B4 b c d e)                   = B5 a b c d e
pushB a (B5 b c d e f)                 = B6 a b c d e f
pushB a (B6 b c d e f g)               = B7 a b c d e f g
pushB a (B7 b c d e f g h)             = B8 a b c d e f g h
pushB a (B8 b c d e f g h i)           = B9 NC.empty a b c d e f g h i NC.empty
pushB a (B9 ncl b c d e f g h i j ncr) = B9 (a NC.<| ncl) b c d e f g h i j ncr

injectB :: Buffer q j k -> q i j -> Buffer q i k
injectB (B1 b)                         a = B2 b a
injectB (B2 b c)                       a = B3 b c a
injectB (B3 b c d)                     a = B4 b c d a
injectB (B4 b c d e)                   a = B5 b c d e a
injectB (B5 b c d e f)                 a = B6 b c d e f a
injectB (B6 b c d e f g)               a = B7 b c d e f g a
injectB (B7 b c d e f g h)             a = B8 b c d e f g h a
injectB (B8 b c d e f g h i)           a = B9 NC.empty b c d e f g h i a NC.empty
injectB (B9 ncl b c d e f g h i j ncr) a = B9 ncl b c d e f g h i j (ncr NC.|> a)

data HPair q r i k where
  H :: !(q j k) -> !(r i j) -> HPair q r i k

data ViewB q i j where
  NoB :: ViewB q i i
  Shift :: Buffer q i j -> ViewB q i j
  NoShift :: Buffer q i j -> ViewB q i j

popB :: Buffer q i k -> HPair q (ViewB q) i k
popB (B1 a)               = a `H` NoB
popB (B2 a b)             = a `H` Shift (B1 b)
popB (B3 a b c)           = a `H` Shift (B2 b c)
popB (B4 a b c d)         = a `H` Shift (B3 b c d)
popB (B5 a b c d e)       = a `H` Shift (B4 b c d e)
popB (B6 a b c d e f)     = a `H` Shift (B5 b c d e f)
popB (B7 a b c d e f g)   = a `H` Shift (B6 b c d e f g)
popB (B8 a b c d e f g h) = a `H` Shift (B7 b c d e f g h)
popB (B9 dp a b c d e f g h i ds) = case NC.uncons dp of
  p1 NC.:| rem1 -> p1 `H` NoShift (B9 rem1 a b c d e f g h i ds)
  NC.Empty -> case NC.uncons ds of
    s1 NC.:| rem1 -> a `H` NoShift (B9 NC.empty b c d e f g h i s1 rem1)
    NC.Empty -> a `H` Shift (B8 b c d e f g h i)

ejectB :: Buffer q i k -> HPair (ViewB q) q i k
ejectB (B1 a)               = NoB `H` a
ejectB (B2 a b)             = Shift (B1 a) `H` b
ejectB (B3 a b c)           = Shift (B2 a b) `H` c
ejectB (B4 a b c d)         = Shift (B3 a b c) `H` d
ejectB (B5 a b c d e)       = Shift (B4 a b c d) `H` e
ejectB (B6 a b c d e f)     = Shift (B5 a b c d e) `H` f
ejectB (B7 a b c d e f g)   = Shift (B6 a b c d e f) `H` g
ejectB (B8 a b c d e f g h) = Shift (B7 a b c d e f g) `H` h
ejectB (B9 dp a b c d e f g h i ds) = case NC.unsnoc ds of
  rem1 NC.:| s1 -> NoShift (B9 dp a b c d e f g h i rem1) `H` s1
  NC.Empty -> case NC.unsnoc dp of
    rem1 NC.:| s1 -> NoShift (B9 rem1 s1 a b c d e f g h NC.empty) `H` i
    NC.Empty -> Shift (B8 a b c d e f g h) `H` i

data StoredTriple q i j where
  S1 :: !(Buffer q j k) -> StoredTriple q j k
  S3 :: !(Buffer q l m) -> Deque (StoredTriple q) k l -> !(Buffer q j k) -> StoredTriple q j m

instance NFData (StoredTriple q i j) where
  rnf !_ = ()

deriving instance Show (StoredTriple q i j)

data OnlyTriple q i j where
  O0  :: !(Buffer q j k) -> OnlyTriple q j k
  ORX :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> OnlyTriple q j m
  OXR :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> OnlyTriple q j m
  OOX :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> OnlyTriple q j m
  OXO :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> OnlyTriple q j m
  OYX :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> OnlyTriple q j m
  OGY :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> OnlyTriple q j m
  OGG :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> OnlyTriple q j m

instance NFData (OnlyTriple ge q i j) where
  rnf !_ = ()

deriving instance Show (OnlyTriple ge q i j)

data LeftTriple q i j where
  L0 :: !(Buffer q k l) -> !(Buffer q j k) -> LeftTriple q j l
  LR :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> LeftTriple q j m
  LO :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> LeftTriple q j m
  LY :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> LeftTriple q j m
  LG :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> LeftTriple q j m

instance NFData (LeftTriple ge q i j) where
  rnf !_ = ()

deriving instance Show (LeftTriple ge q i j)

data Cap (r :: (* -> * -> *) -> * -> * -> *) (t :: * -> * -> *) u b where
  Opening :: Cap r s t u
  Triple :: Repairable r => !(r q i j) -> Cap r q i j
  Cap :: Repairable r' => !(r q i j) -> !(r' q' s t) -> Cap r q i j

class Repairable (r :: (* -> * -> *) -> * -> * -> *) where
  repair :: r q i j -> r q i j

instance Show (Cap r t u b) where
  show Opening = "Opening"
  show (Triple _) = "Triple"
  show (Cap _ _) = "Cap"

data Nope (b :: * -> * -> *) c d

data Colour = Red | Green

data Dir = Le | Ri

data RightTriple (q :: * -> * -> *) i j where
  R0 :: !(Buffer q k l) -> !(Buffer q j k) -> RightTriple q j l
  RR :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> RightTriple q j m
  RO :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> RightTriple q j m
  RY :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> RightTriple q j m
  RG :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> RightTriple q j m

instance NFData (RightTriple q i j) where
  rnf !_ = ()

deriving instance Show (RightTriple q i j)

data Deque q i j where
  D0 :: Deque q i i
  D2 :: !(Cap LeftTriple q j k) -> !(Cap RightTriple q i j) -> Deque q i k
  DOL :: !(Cap OnlyTriple q i j) -> Deque q i j
  DOR :: !(Cap OnlyTriple q i j) -> Deque q i j

instance NFData (Deque q i j) where
  rnf !_ = ()

deriving instance Show (Deque q i j)

cap :: Repairable r' => Cap r q i j -> r' s t u -> Cap r q i j
cap Opening t = Triple t
cap (Triple c) t = Cap c t

singleton :: q i j -> Deque q i j
singleton a = DOL (Triple (O0 (B1 a)))

empty :: Deque q i i
empty = D0

plugL :: Repairable r => r s t u -> Deque q i j -> Deque q i j
plugL c (D2 l r) = D2 (cap l c) r
plugL c (DOL ot) = DOL (cap ot c)

plugR :: Repairable r => Deque q i j -> r s t u -> Deque q i j
plugR (D2 l rt) c = D2 l (cap rt c)
plugR (DOR ot) c = DOR (cap ot c)

data ViewCap r q i j where
  ViewCap :: Repairable r' => Cap r q i j -> r' s t u -> ViewCap r q i j

uncap :: Repairable r => Cap r q i j -> ViewCap r q i j
uncap (Triple c) = ViewCap Opening c
uncap (Cap o c) = ViewCap (Triple o) c

push :: q j k -> Deque q i j -> Deque q i k
push a D0       = DOL (Triple (O0 (B1 a)))
push a (D2 l r) = D2 (pushLeft a l) r
push a (DOL o)  = DOL (pushOnly a o)
push a (DOR o)  = DOR (pushOnly a o)

inject :: Deque q j k -> q i j -> Deque q i k
inject D0       a = DOL (Triple (O0 (B1 a)))
inject (D2 l r) a = D2 l (injectRight r a)
inject (DOL o)  a = DOL (injectOnly o a)
inject (DOR o)  a = DOR (injectOnly o a)

injectRight :: Cap RightTriple q j k -> q i j -> Cap RightTriple q i k
injectRight (Triple (R0 bl br))              a      = Triple (R0 bl (injectB br a))
injectRight (Cap (RO bl (D2 lt rt) br) cap1) a      = case uncap lt of ViewCap lt2 cap2 -> Cap (RY bl (D2 lt2 (cap rt cap1)) (injectB br a)) cap2
injectRight (Cap (RO bl (DOR ot) br) cap1)   a      = Cap (RY bl (DOL ot) (injectB br a)) cap1
injectRight (Cap (RY bl (D2 lt rt) br) cap1) a      = Triple (RG bl (D2 (cap lt cap1) rt) (injectB br a))
injectRight (Cap (RY bl (DOL ot) br) cap1)   a      = Triple (RG bl (DOL (cap ot cap1)) (injectB br a))
injectRight (Triple (RG bl d br))            a      = Triple (RG bl d (injectB br a))
injectRight (Triple (RR bl (D2 lt rt) br))   a      = case uncap rt of ViewCap rt2 cap2 -> Cap (RO bl (D2 lt rt2) (injectB br a)) cap2
injectRight (Triple (RR bl (DOL ot) br))     a      = case uncap ot of ViewCap ot2 cap2 -> Cap (RO bl (DOR ot2) (injectB br a)) cap2
injectRight (Triple (RR bl (DOR ot) br))     a      = case uncap ot of ViewCap ot2 cap2 -> Cap (RO bl (DOR ot2) (injectB br a)) cap2
injectRight (Triple (RR bl D0 br))           a      = Triple (R0 bl (injectB br a))

injectOnly :: Cap OnlyTriple q j k -> q i j -> Cap OnlyTriple q i k
injectOnly (Triple (O0 b))                        a = Triple (O0 (injectB b a))
injectOnly (Cap (OOX bl d br) cap1)               a = Cap (OOX bl d (injectB br a)) cap1
injectOnly (Cap (OXO bl@B7{} (D2 lt rt) br) cap1) a = case uncap lt of ViewCap lt2 cap2 -> Cap (OYX bl (D2 lt2 (cap rt cap1)) (injectB br a)) cap2
injectOnly (Cap (OXO bl@B7{} (DOR ot) br) cap1)   a = Cap (OYX bl (DOL ot) (injectB br a)) cap1
injectOnly (Cap (OXO bl@B8{} (D2 lt rt) br) cap1) a = case uncap lt of ViewCap lt2 cap2 -> Cap (OGY bl (D2 lt2 (cap rt cap1)) (injectB br a)) cap2
injectOnly (Cap (OXO bl@B8{} (DOR ot) br) cap1)   a = Cap (OGY bl (DOL ot) (injectB br a)) cap1
injectOnly (Cap (OXO bl@B9{} (D2 lt rt) br) cap1) a = case uncap lt of ViewCap lt2 cap2 -> Cap (OGY bl (D2 lt2 (cap rt cap1)) (injectB br a)) cap2
injectOnly (Cap (OXO bl@B9{} (DOR ot) br) cap1)   a = Cap (OGY bl (DOL ot) (injectB br a)) cap1
injectOnly (Cap (OYX bl d br) cap1)               a = Cap (OYX bl d (injectB br a)) cap1
injectOnly (Cap (OGY bl d br) cap1)               a = Triple (OGG bl (plugL cap1 d) (injectB br a))
injectOnly (Triple (OGG bl d br))                 a = Triple (OGG bl d (injectB br a))
injectOnly (Triple (ORX bl d br))                 a = Triple (ORX bl d (injectB br a))
injectOnly (Triple (OXR bl D0 br))                a = Triple (O0 (injectB (catenateB bl br) a))
injectOnly (Triple (OXR bl@B6{} (D2 lt rt) br))   a = case uncap rt of ViewCap rt2 cap2 -> Cap (OOX bl (D2 lt rt2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B6{} (DOL ot) br))     a = case uncap ot of ViewCap ot2 cap2 -> Cap (OOX bl (DOR ot2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B6{} (DOR ot) br))     a = case uncap ot of ViewCap ot2 cap2 -> Cap (OOX bl (DOR ot2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B7{} (D2 lt rt) br))   a = case uncap rt of ViewCap rt2 cap2 -> Cap (OXO bl (D2 lt rt2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B7{} (DOL ot) br))     a = case uncap ot of ViewCap ot2 cap2 -> Cap (OXO bl (DOR ot2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B7{} (DOR ot) br))     a = case uncap ot of ViewCap ot2 cap2 -> Cap (OXO bl (DOR ot2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B8{} (D2 lt rt) br))   a = case uncap rt of ViewCap rt2 cap2 -> Cap (OXO bl (D2 lt rt2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B8{} (DOL ot) br))     a = case uncap ot of ViewCap ot2 cap2 -> Cap (OXO bl (DOR ot2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B8{} (DOR ot) br))     a = case uncap ot of ViewCap ot2 cap2 -> Cap (OXO bl (DOR ot2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B9{} (D2 lt rt) br))   a = case uncap rt of ViewCap rt2 cap2 -> Cap (OXO bl (D2 lt rt2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B9{} (DOL ot) br))     a = case uncap ot of ViewCap ot2 cap2 -> Cap (OXO bl (DOR ot2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B9{} (DOR ot) br))     a = case uncap ot of ViewCap ot2 cap2 -> Cap (OXO bl (DOR ot2) (injectB br a)) cap2

pushLeft :: q j k -> Cap LeftTriple q i j -> Cap LeftTriple q i k
pushLeft a (Triple (L0 bl br))                   = Triple (L0 (pushB a bl) br)
pushLeft a (Cap (LO bl (D2 lt rt) br) cap1)      = case uncap lt of ViewCap lt2 cap2 -> Cap (LY (pushB a bl) (D2 lt2 (cap rt cap1)) br) cap2
pushLeft a (Cap (LO bl (DOR ot) br) cap1)        = Cap (LY (pushB a bl) (DOL ot) br) cap1
pushLeft a (Cap (LY bl (D2 lt rt) br) cap1)      = Triple (LG (pushB a bl) (D2 (cap lt cap1) rt) br)
pushLeft a (Cap (LY bl (DOL ot) br) cap1)        = Triple (LG (pushB a bl) (DOL (cap ot cap1)) br)
pushLeft a (Triple (LR bl D0 br))                = Triple (L0 (pushB a bl) br)
pushLeft a (Triple (LR bl (D2 lt rt) br))        = case uncap rt of ViewCap rt2 cap2 -> Cap (LO (pushB a bl) (D2 lt rt2) br) cap2
pushLeft a (Triple (LR bl (DOL ot) br))          = case uncap ot of ViewCap ot2 cap2 -> Cap (LO (pushB a bl) (DOR ot2) br) cap2
pushLeft a (Triple (LR bl (DOR ot) br))          = case uncap ot of ViewCap ot2 cap2 -> Cap (LO (pushB a bl) (DOR ot2) br) cap2
pushLeft a (Triple (LG bl d br))                 = Triple (LG (pushB a bl) d br)

pushOnly :: q j k -> Cap OnlyTriple (Closed cl) q i j -> Cap OnlyTriple q i k
pushOnly a (Triple (O0 b))                        = Triple (O0 (pushB a b))
pushOnly a (Cap (OOX bl d br@B6{}) cap1)          = Cap (OXO (pushB a bl) d br) cap1
pushOnly a (Cap (OOX bl (D2 lt rt) br@B7{}) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (OYX (pushB a bl) (D2 lt2 (cap rt cap1)) br) cap2
pushOnly a (Cap (OOX bl (DOR ot) br@B7{}) cap1)   = Cap (OYX (pushB a bl) (DOL ot) br) cap1
pushOnly a (Cap (OOX bl (D2 lt rt) br@B8{}) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (OYX (pushB a bl) (D2 lt2 (cap rt cap1)) br) cap2
pushOnly a (Cap (OOX bl (DOR ot) br@B8{}) cap1)   = Cap (OYX (pushB a bl) (DOL ot) br) cap1
pushOnly a (Cap (OOX bl (D2 lt rt) br@B9{}) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (OYX (pushB a bl) (D2 lt2 (cap rt cap1)) br) cap2
pushOnly a (Cap (OOX bl (DOR ot) br@B9{}) cap1)   = Cap (OYX (pushB a bl) (DOL ot) br) cap1
pushOnly a (Cap (OXO bl d br) cap1)               = Cap (OXO (pushB a bl) d br) cap1
pushOnly a (Cap (OYX bl d br@B7{}) cap1)          = Cap (OGY (pushB a bl) d br) cap1
pushOnly a (Cap (OYX bl (D2 lt rt) br@B8{}) cap1) = Triple (OGG (pushB a bl) (D2 (cap lt cap1) rt) br)
pushOnly a (Cap (OYX bl (DOL ot) br@B8{}) cap1)   = Triple (OGG (pushB a bl) (DOL (cap ot cap1)) br)
pushOnly a (Cap (OYX bl (D2 lt rt) br@B9{}) cap1) = Triple (OGG (pushB a bl) (D2 (cap lt cap1) rt) br)
pushOnly a (Cap (OYX bl (DOL ot) br@B9{}) cap1)   = Triple (OGG (pushB a bl) (DOL (cap ot cap1)) br)
pushOnly a (Cap (OGY bl d br) cap1)               = Cap (OGY (pushB a bl) d br) cap1
pushOnly a (Triple (OGG bl d br))                 = Triple (OGG (pushB a bl) d br)
pushOnly a (Triple (ORX bl d br@B5{}))            = Triple (OXR (pushB a bl) d br)
pushOnly a (Triple (ORX bl D0         br))        = Triple (O0 (catenateB (pushB a bl) br))
pushOnly a (Triple (ORX bl (D2 lt rt) br@B6{}))   = case uncap rt of ViewCap rt2 cap2 -> Cap (OOX (pushB a bl) (D2 lt rt2) br) cap2
pushOnly a (Triple (ORX bl (DOL ot)   br@B6{}))   = case uncap ot of ViewCap ot2 cap2 -> Cap (OOX (pushB a bl) (DOR ot2) br) cap2
pushOnly a (Triple (ORX bl (DOR ot)   br@B6{}))   = case uncap ot of ViewCap ot2 cap2 -> Cap (OOX (pushB a bl) (DOR ot2) br) cap2
pushOnly a (Triple (ORX bl (D2 lt rt) br@B7{}))   = case uncap rt of ViewCap rt2 cap2 -> Cap (OOX (pushB a bl) (D2 lt rt2) br) cap2
pushOnly a (Triple (ORX bl (DOL ot)   br@B7{}))   = case uncap ot of ViewCap ot2 cap2 -> Cap (OOX (pushB a bl) (DOR ot2) br) cap2
pushOnly a (Triple (ORX bl (DOR ot)   br@B7{}))   = case uncap ot of ViewCap ot2 cap2 -> Cap (OOX (pushB a bl) (DOR ot2) br) cap2
pushOnly a (Triple (ORX bl (D2 lt rt) br@B8{}))   = case uncap rt of ViewCap rt2 cap2 -> Cap (OOX (pushB a bl) (D2 lt rt2) br) cap2
pushOnly a (Triple (ORX bl (DOL ot)   br@B8{}))   = case uncap ot of ViewCap ot2 cap2 -> Cap (OOX (pushB a bl) (DOR ot2) br) cap2
pushOnly a (Triple (ORX bl (DOR ot)   br@B8{}))   = case uncap ot of ViewCap ot2 cap2 -> Cap (OOX (pushB a bl) (DOR ot2) br) cap2
pushOnly a (Triple (ORX bl (D2 lt rt) br@B9{}))   = case uncap rt of ViewCap rt2 cap2 -> Cap (OOX (pushB a bl) (D2 lt rt2) br) cap2
pushOnly a (Triple (ORX bl (DOL ot)   br@B9{}))   = case uncap ot of ViewCap ot2 cap2 -> Cap (OOX (pushB a bl) (DOR ot2) br) cap2
pushOnly a (Triple (ORX bl (DOR ot)   br@B9{}))   = case uncap ot of ViewCap ot2 cap2 -> Cap (OOX (pushB a bl) (DOR ot2) br) cap2
pushOnly a (Triple (OXR bl d br))                 = Triple (OXR (pushB a bl) d br)

catenateB :: Buffer q j k -> Buffer q i j -> Buffer q i k
catenateB B9{} B9{} = error "Bad"
catenateB (B1 a) br@B1{} = pushB a br
catenateB (B1 a) br@B2{} = pushB a br
catenateB (B1 a) br@B3{} = pushB a br
catenateB (B1 a) br@B4{} = pushB a br
catenateB (B1 a) br@B5{} = pushB a br
catenateB (B1 a) br@B6{} = pushB a br
catenateB (B1 a) br@B7{} = pushB a br
catenateB (B1 a) br@B8{} = pushB a br
catenateB (B1 a) br@B9{} = pushB a br
catenateB (B2 a b) br@B1{} = pushB a $ pushB b $ br
catenateB (B2 a b) br@B2{} = pushB a $ pushB b $ br
catenateB (B2 a b) br@B3{} = pushB a $ pushB b $ br
catenateB (B2 a b) br@B4{} = pushB a $ pushB b $ br
catenateB (B2 a b) br@B5{} = pushB a $ pushB b $ br
catenateB (B2 a b) br@B6{} = pushB a $ pushB b $ br
catenateB (B2 a b) br@B7{} = pushB a $ pushB b $ br
catenateB (B2 a b) br@B8{} = pushB a $ pushB b $ br
catenateB (B2 a b) br@B9{} = pushB a $ pushB b $ br
catenateB (B3 a b c) br@B1{} = pushB a $ pushB b $ pushB c $ br
catenateB (B3 a b c) br@B2{} = pushB a $ pushB b $ pushB c $ br
catenateB (B3 a b c) br@B3{} = pushB a $ pushB b $ pushB c $ br
catenateB (B3 a b c) br@B4{} = pushB a $ pushB b $ pushB c $ br
catenateB (B3 a b c) br@B5{} = pushB a $ pushB b $ pushB c $ br
catenateB (B3 a b c) br@B6{} = pushB a $ pushB b $ pushB c $ br
catenateB (B3 a b c) br@B7{} = pushB a $ pushB b $ pushB c $ br
catenateB (B3 a b c) br@B8{} = pushB a $ pushB b $ pushB c $ br
catenateB (B3 a b c) br@B9{} = pushB a $ pushB b $ pushB c $ br
catenateB (B4 a b c d) br@B1{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B4 a b c d) br@B2{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B4 a b c d) br@B3{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B4 a b c d) br@B4{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B4 a b c d) br@B5{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B4 a b c d) br@B6{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B4 a b c d) br@B7{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B4 a b c d) br@B8{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B4 a b c d) br@B9{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B5 a b c d e) br@B1{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B5 a b c d e) br@B2{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B5 a b c d e) br@B3{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B5 a b c d e) br@B4{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B5 a b c d e) br@B5{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B5 a b c d e) br@B6{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B5 a b c d e) br@B7{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B5 a b c d e) br@B8{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B5 a b c d e) br@B9{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B6 a b c d e f) br@B1{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B6 a b c d e f) br@B2{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B6 a b c d e f) br@B3{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B6 a b c d e f) br@B4{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B6 a b c d e f) br@B5{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B6 a b c d e f) br@B6{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B6 a b c d e f) br@B7{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B6 a b c d e f) br@B8{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B6 a b c d e f) br@B9{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B7 a b c d e f g) br@B1{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B7 a b c d e f g) br@B2{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B7 a b c d e f g) br@B3{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B7 a b c d e f g) br@B4{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B7 a b c d e f g) br@B5{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B7 a b c d e f g) br@B6{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B7 a b c d e f g) br@B7{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B7 a b c d e f g) br@B8{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B7 a b c d e f g) br@B9{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B8 a b c d e f g h) br@B1{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB (B8 a b c d e f g h) br@B2{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB (B8 a b c d e f g h) br@B3{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB (B8 a b c d e f g h) br@B4{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB (B8 a b c d e f g h) br@B5{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB (B8 a b c d e f g h) br@B6{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB (B8 a b c d e f g h) br@B7{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB (B8 a b c d e f g h) br@B8{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB (B8 a b c d e f g h) br@B9{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB bl@B9{} (B1 a) = injectB bl a
catenateB bl@B9{} (B2 a b) = injectB (injectB bl a) b
catenateB bl@B9{} (B3 a b c) = injectB (injectB (injectB bl a) b) c
catenateB bl@B9{} (B4 a b c d) = injectB (injectB (injectB (injectB bl a) b) c) d
catenateB bl@B9{} (B5 a b c d e) = injectB (injectB (injectB (injectB (injectB bl a) b) c) d) e
catenateB bl@B9{} (B6 a b c d e f) = injectB (injectB (injectB (injectB (injectB (injectB bl a) b) c) d) e) f
catenateB bl@B9{} (B7 a b c d e f g) = injectB (injectB (injectB (injectB (injectB (injectB (injectB bl a) b) c) d) e) f) g
catenateB bl@B9{} (B8 a b c d e f g h) = injectB (injectB (injectB (injectB (injectB (injectB (injectB (injectB bl a) b) c) d) e) f) g) h

catenate :: Deque q j k -> Deque q i j -> Deque q i k
-- Trivial
catenate D0 a = a
catenate a D0 = a
-- Case 4:
catenate (DOL (Triple (O0 bl@B8{}))) (DOL (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOL (Triple (O0 bl@B8{}))) (DOL (Triple (O0 br@B9{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOL (Triple (O0 bl@B9{}))) (DOL (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOL (Triple (O0 bl@B9{}))) (DOL (Triple (O0 br@B9{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOL (Triple (O0 bl)))      (DOL (Triple (O0 br)))      = DOL (Triple (O0 (catenateB bl br)))
catenate (DOL (Triple (O0 bl@B8{}))) (DOR (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOL (Triple (O0 bl@B8{}))) (DOR (Triple (O0 br@B9{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOL (Triple (O0 bl@B9{}))) (DOR (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOL (Triple (O0 bl@B9{}))) (DOR (Triple (O0 br@B9{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOL (Triple (O0 bl)))      (DOR (Triple (O0 br)))      = DOL (Triple (O0 (catenateB bl br)))
catenate (DOR (Triple (O0 bl@B8{}))) (DOL (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOR (Triple (O0 bl@B8{}))) (DOL (Triple (O0 br@B9{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOR (Triple (O0 bl@B9{}))) (DOL (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOR (Triple (O0 bl@B9{}))) (DOL (Triple (O0 br@B9{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOR (Triple (O0 bl)))      (DOL (Triple (O0 br)))      = DOL (Triple (O0 (catenateB bl br)))
catenate (DOR (Triple (O0 bl@B8{}))) (DOR (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOR (Triple (O0 bl@B8{}))) (DOR (Triple (O0 br@B9{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOR (Triple (O0 bl@B9{}))) (DOR (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOR (Triple (O0 bl@B9{}))) (DOR (Triple (O0 br@B9{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOR (Triple (O0 bl)))      (DOR (Triple (O0 br)))      = DOL (Triple (O0 (catenateB bl br)))
-- Case 2:
catenate (DOL (Triple (O0 bl))) (D2 lt rt) = D2 (onlyL bl lt) rt
catenate (DOR (Triple (O0 bl))) (D2 lt rt) = D2 (onlyL bl lt) rt
-- Case 3
catenate (D2 lt rt) (DOL (Triple (O0 br))) = D2 lt (onlyR rt br)
catenate (D2 lt rt) (DOR (Triple (O0 br))) = D2 lt (onlyR rt br)
-- Case 1
catenate d e = D2 (fixLeft d) (fixRight e)

catenate' :: Deque q j k -> Deque q i j -> Deque q i k
-- Trivial
catenate' D0 a = a
catenate' a D0 = a
-- Case 4:
catenate' (DOL (Triple (O0 bl@B8{}))) (DOL (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOL (Triple (O0 bl)))      (DOL (Triple (O0 br)))      = DOL (Triple (O0 (catenateB bl br)))
catenate' (DOL (Triple (O0 bl@B8{}))) (DOR (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOL (Triple (O0 bl)))      (DOR (Triple (O0 br)))      = DOL (Triple (O0 (catenateB bl br)))
catenate' (DOR (Triple (O0 bl@B8{}))) (DOL (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOR (Triple (O0 bl)))      (DOL (Triple (O0 br)))      = DOL (Triple (O0 (catenateB bl br)))
catenate' (DOR (Triple (O0 bl@B8{}))) (DOR (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOR (Triple (O0 bl)))      (DOR (Triple (O0 br)))      = DOL (Triple (O0 (catenateB bl br)))
-- Case 2:
catenate' (DOL (Triple (O0 bl))) (D2 lt rt) = D2 (onlyL bl lt) rt
catenate' (DOR (Triple (O0 bl))) (D2 lt rt) = D2 (onlyL bl lt) rt
-- Case 3
catenate' (D2 lt rt) (DOL (Triple (O0 br))) = D2 lt (onlyR rt br)
catenate' (D2 lt rt) (DOR (Triple (O0 br))) = R2 lt (onlyR rt br)
-- Case 1
catenate' d e = D2 (fixLeft d) (fixRight e)

onlyL :: Buffer q j k -> Cap LeftTriple q i j -> Cap LeftTriple q i k
onlyL bl@B8{} (Triple (L0 ll lr))              = Triple (LG bl (push (S1 ll) D0) lr)
onlyL bl@B8{} (Cap (LO ll d lr) cap1)          = Triple (LG bl (push (S1 ll) (plugR d cap1)) lr)
onlyL bl@B8{} (Cap (LY ll d lr) cap1)          = Triple (LG bl (push (S1 ll) (plugL cap1 d)) lr)
onlyL bl@B8{} (Triple (LG ll d lr))            = Triple (LG bl (push (S1 ll) d) lr)
onlyL bl@B8{} (Triple (LR ll d lr))            = Triple (LG bl (push (S1 ll) d) lr)
onlyL bl@B9{} (Triple (L0 ll lr))              = Triple (LG bl (push (S1 ll) D0) lr)
onlyL bl@B9{} (Cap (LO ll d lr) cap1)          = Triple (LG bl (push (S1 ll) (plugR d cap1)) lr)
onlyL bl@B9{} (Cap (LY ll d lr) cap1)          = Triple (LG bl (push (S1 ll) (plugL cap1 d)) lr)
onlyL bl@B9{} (Triple (LG ll d lr))            = Triple (LG bl (push (S1 ll) d) lr)
onlyL bl@B9{} (Triple (LR ll d lr))            = Triple (LG bl (push (S1 ll) d) lr)
onlyL bl      (Triple (L0 ll lr))              = Triple (L0 (catenateB bl ll) lr)
onlyL bl@B1{} (Triple (LR ll D0 lr))           = Triple (L0 (catenateB bl ll) lr)
onlyL bl@B1{} (Triple (LR ll (D2 lt rt) lr))   = case uncap rt of ViewCap rt2 cap2 -> Cap (LO (catenateB bl ll) (D2 lt rt2) lr) cap2
onlyL bl@B1{} (Triple (LR ll (DOL ot) lr))     = case uncap ot of ViewCap ot2 cap2 -> Cap (LO (catenateB bl ll) (DOR ot2) lr) cap2
onlyL bl@B1{} (Triple (LR ll (DOR ot) lr))     = case uncap ot of ViewCap ot2 cap2 -> Cap (LO (catenateB bl ll) (DOR ot2) lr) cap2
onlyL bl@B2{} (Triple (LR ll D0 lr))           = Triple (L0 (catenateB bl ll) lr)
onlyL bl@B2{} (Triple (LR ll (D2 lt rt) lr))   = case uncap lt of ViewCap lt2 cap2 -> Cap (LY (catenateB bl ll) (D2 lt2 rt) lr) cap2
onlyL bl@B2{} (Triple (LR ll (DOL ot) lr))     = case uncap ot of ViewCap ot2 cap2 -> Cap (LY (catenateB bl ll) (DOL ot2) lr) cap2
onlyL bl@B2{} (Triple (LR ll (DOR ot) lr))     = case uncap ot of ViewCap ot2 cap2 -> Cap (LY (catenateB bl ll) (DOL ot2) lr) cap2
onlyL bl@B3{} (Triple (LR ll d lr))            = Triple (LG (catenateB bl ll) d lr)
onlyL bl@B4{} (Triple (LR ll d lr))            = Triple (LG (catenateB bl ll) d lr)
onlyL bl@B5{} (Triple (LR ll d lr))            = Triple (LG (catenateB bl ll) d lr)
onlyL bl@B6{} (Triple (LR ll d lr))            = Triple (LG (catenateB bl ll) d lr)
onlyL bl@B7{} (Triple (LR ll d lr))            = Triple (LG (catenateB bl ll) d lr)
onlyL bl@B1{} (Cap (LO ll (D2 lt rt) lr) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (LY (catenateB bl ll) (D2 lt2 (cap rt cap1)) lr) cap2
onlyL bl@B1{} (Cap (LO ll (DOR ot) lr) cap1)   = Cap (LY (catenateB bl ll) (DOL ot) lr) cap1
onlyL bl@B2{} (Cap (LO ll d lr) cap1)          = Triple (LG (catenateB bl ll) d2 lr) where d2 = plugR d cap1
onlyL bl@B3{} (Cap (LO ll d lr) cap1)          = Triple (LG (catenateB bl ll) d2 lr) where d2 = plugR d cap1
onlyL bl@B4{} (Cap (LO ll d lr) cap1)          = Triple (LG (catenateB bl ll) d2 lr) where d2 = plugR d cap1
onlyL bl@B5{} (Cap (LO ll d lr) cap1)          = Triple (LG (catenateB bl ll) d2 lr) where d2 = plugR d cap1
onlyL bl@B6{} (Cap (LO ll d lr) cap1)          = Triple (LG (catenateB bl ll) d2 lr) where d2 = plugR d cap1
onlyL bl@B7{} (Cap (LO ll d lr) cap1)          = Triple (LG (catenateB bl ll) d2 lr) where d2 = plugR d cap1
onlyL bl      (Cap (LY ll d lr) cap1)          = Triple (LG (catenateB bl ll) d2 lr) where d2 = plugL cap1 d
onlyL bl      (Triple (LG ll d lr))            = Triple (LG (catenateB bl ll) d lr)

onlyR :: Cap RightTriple q j k -> Buffer q i j -> Cap RightTriple q i k
onlyR (Triple (R0 rl rr))              br@B8{} = Triple (RG rl (inject D0 (S1 rr)) br)
onlyR (Cap (RO rl d rr) cap1)          br@B8{} = Triple (RG rl (inject (plugR d cap1) (S1 rr)) br)
onlyR (Cap (RY rl d rr) cap1)          br@B8{} = Triple (RG rl (inject (plugL cap1 d) (S1 rr)) br)
onlyR (Triple (RG rl d rr))            br@B8{} = Triple (RG rl (inject d (S1 rr)) br)
onlyR (Triple (RR rl d rr))            br@B8{} = Triple (RG rl (inject d (S1 rr)) br)
onlyR (Triple (R0 rl rr))              br@B9{} = Triple (RG rl (inject D0 (S1 rr)) br)
onlyR (Cap (RO rl d rr) cap1)          br@B9{} = Triple (RG rl (inject (plugR d cap1) (S1 rr)) br)
onlyR (Cap (RY rl d rr) cap1)          br@B9{} = Triple (RG rl (inject (plugL cap1 d) (S1 rr)) br)
onlyR (Triple (RG rl d rr))            br@B9{} = Triple (RG rl (inject d (S1 rr)) br)
onlyR (Triple (RR rl d rr))            br@B9{} = Triple (RG rl (inject d (S1 rr)) br)
onlyR (Triple (R0 rl rr))              br      = Triple (R0 rl (catenateB rr br))
onlyR (Triple (RR rl D0 rr))           br@B1{} = Triple (R0 rl (catenateB rr br))
onlyR (Triple (RR rl (D2 lt rt) rr))   br@B1{} = case uncap rt of ViewCap rt2 cap2 -> Cap (RO rl (D2 lt rt2) (catenateB rr br)) cap2
onlyR (Triple (RR rl (DOR ot) rr))     br@B1{} = case uncap ot of ViewCap ot2 cap2 -> Cap (RO rl (DOR ot2) (catenateB rr br)) cap2
onlyR (Triple (RR rl (DOL ot) rr))     br@B1{} = case uncap ot of ViewCap ot2 cap2 -> Cap (RO rl (DOR ot2) (catenateB rr br)) cap2
onlyR (Triple (RR rl D0 rr))           br@B2{} = Triple (R0 rl (catenateB rr br))
onlyR (Triple (RR rl (D2 lt rt) rr))   br@B2{} = case uncap lt of ViewCap lt2 cap2 -> Cap (RY rl (D2 lt2 rt) (catenateB rr br)) cap2
onlyR (Triple (RR rl (DOR ot) rr))     br@B2{} = case uncap ot of ViewCap ot2 cap2 -> Cap (RY rl (DOL ot2) (catenateB rr br)) cap2
onlyR (Triple (RR rl (DOL ot) rr))     br@B2{} = case uncap ot of ViewCap ot2 cap2 -> Cap (RY rl (DOL ot2) (catenateB rr br)) cap2
onlyR (Triple (RR rl d rr))            br@B3{} = Triple (RG rl d (catenateB rr br))
onlyR (Triple (RR rl d rr))            br@B4{} = Triple (RG rl d (catenateB rr br))
onlyR (Triple (RR rl d rr))            br@B5{} = Triple (RG rl d (catenateB rr br))
onlyR (Triple (RR rl d rr))            br@B6{} = Triple (RG rl d (catenateB rr br))
onlyR (Triple (RR rl d rr))            br@B7{} = Triple (RG rl d (catenateB rr br))
onlyR (Cap (RO rl (D2 lt rt) rr) cap1) br@B1{} = case uncap lt of ViewCap lt2 cap2 -> Cap (RY rl (D2 lt2 (cap rt cap1)) (catenateB rr br)) cap2
onlyR (Cap (RO rl (DOR ot) rr) cap1)   br@B1{} = Cap (RY rl (DOL ot) (catenateB rr br)) cap1
onlyR (Cap (RO rl d rr) cap1)          br@B2{} = Triple (RG rl d2 (catenateB rr br)) where d2 = plugR d cap1
onlyR (Cap (RO rl d rr) cap1)          br@B3{} = Triple (RG rl d2 (catenateB rr br)) where d2 = plugR d cap1
onlyR (Cap (RO rl d rr) cap1)          br@B4{} = Triple (RG rl d2 (catenateB rr br)) where d2 = plugR d cap1
onlyR (Cap (RO rl d rr) cap1)          br@B5{} = Triple (RG rl d2 (catenateB rr br)) where d2 = plugR d cap1
onlyR (Cap (RO rl d rr) cap1)          br@B6{} = Triple (RG rl d2 (catenateB rr br)) where d2 = plugR d cap1
onlyR (Cap (RO rl d rr) cap1)          br@B7{} = Triple (RG rl d2 (catenateB rr br)) where d2 = plugR d cap1
onlyR (Cap (RY rl d rr) cap1)          br      = Triple (RG rl d2 (catenateB rr br)) where d2 = plugL cap1 d
onlyR (Triple (RG rl d rr))            br      = Triple (RG rl d (catenateB rr br))

data Aux q i l where
  Aux :: Buffer q k l -> q k l -> q i j -> Section q i l

fixLeft :: Deque q i j -> Cap LeftTriple q i j
fixLeft d = case d of
  D0 -> error "Impossible"
  (DOL c) -> only c
  (DOR c) -> only c
  (D2 (Triple (LG p1 D0 s1)) (Triple (R0 p2 s2@B9{}))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  (D2 (Triple (LG p1 D0 s1)) (Triple (R0 p2 s2@B8{}))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  (D2 (Triple (LG p1 D0 s1)) (Triple (R0 p2 s2))) -> only (Triple (O0 (catenateB (catenateB (catenateB p1 s1) p2) s2)))
  (D2 (Triple (LG p1 D0 s1)) (Triple (RG p2 d2 s2))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) d2 s2))
  (D2 (Triple (LG p1 D0 s1)) (Cap (RO p2 d2 s2) c)) -> only (Cap (OXO (catenateB (catenateB p1 s1) p2) d2 s2) c)
  (D2 (Triple (LG p1 D0 s1)) (Cap (RY p2 d2 s2) c)) -> only (Cap (OGY (catenateB (catenateB p1 s1) p2) d2 s2) c)
  (D2 (Triple (L0 p1 s1)) (Triple (R0 p2 s2@B9{}))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  (D2 (Triple (L0 p1 s1)) (Triple (R0 p2 s2@B8{}))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  (D2 (Triple (L0 p1 s1)) (Triple (R0 p2 s2))) -> only (Triple (O0 (catenateB (catenateB (catenateB p1 s1) p2) s2)))
  (D2 (Triple (L0 p1 s1)) (Triple (RG p2 d2 s2))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) d2 s2))
  (D2 (Triple (L0 p1 s1)) (Cap (RO p2 d2 s2) c)) -> only (Cap (OXO (catenateB (catenateB p1 s1) p2) d2 s2) c)
  (D2 (Triple (L0 p1 s1)) (Cap (RY p2 d2 s2) c)) -> only (Cap (OGY (catenateB (catenateB p1 s1) p2) d2 s2) c)
  (D2 (Triple (LG p1 d1 s1)) (Triple (RG p2 d2 s2))) -> case aux s2 of H rem2 b2 -> Triple $ LG p1 (inject d1 (S3 (catenateB s1 p2) d2 rem2)) b2
  (D2 (Triple (LG p1 d1 s1)) (Triple (R0 p2 s2))) -> case aux s2 of H rem2 b2 -> Triple $ LG p1 (inject d1 (S3 (catenateB s1 p2) D0 rem2)) b2
  (D2 (Triple (LG p1 d1 s1)) (Cap (RY p2 d2 s2) c)) -> case aux s2 of H rem2 b2 -> Triple $ LG p1 (inject d1 (S3 (catenateB s1 p2) (plugL c d2) rem2)) b2
  (D2 (Triple (LG p1 d1 s1)) (Cap (RO p2 d2 s2) c)) -> case aux s2 of H rem2 b2 -> Triple $ LG p1 (inject d1 (S3 (catenateB s1 p2) (plugR d2 c) rem2)) b2
  (D2 (Cap (LY p1 d1 s1) cl) (Triple (RG p2 d2 s2))) -> case aux s2 of
    H rem2 b2 -> case d1 of
      D2 d1l d1r -> Cap (LY p1 (D2 d11 (injectRight d1r (S3 (catenateB s1 p2) d2 rem2))) b2) cl
      DOL ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) d2 rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) b2) c2
  (D2 (Cap (LY p1 d1 s1) cl) (Triple (R0 p2 s2))) -> case aux s2 of
    H rem2 b2 -> case d1 of
      D2 d1l d1r -> Cap (LY p1 (D2 d1l ( injectRight d1r (S3 (catenateB s1 p2) D0 rem2))) b2) cl
      DOL ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) D0 rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) b2) c2
  (D2 (Cap (LY p1 d1 s1) cl) (Cap (RY p2 d2 s2) c)) -> case aux s2 of 
    H rem2 b2 -> case d1 of
      D2 d1l d1r -> Cap (LY p1 (D2 d1l (injectRight d1r (S3 (catenateB s1 p2) (plugL c d2) rem2))) b2) cl
      DOL ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) (plugL c d2) rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) b2) c2
  (D2 (Cap (LY p1 d1 s1) cl) (Cap (RO p2 d2 s2) c)) -> case aux s2 of 
    H rem2 b2 case d1 of
      D2 d1l d1r -> Cap (LY p1 (D2 d1l (injectRight d1r (S3 (catenateB s1 p2) (plugR d2 c) rem2))) b2) cl
      DOL ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) (plugR d2 c) rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) b2) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Triple (RG p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> case uncap (injectRight (cap d1r cl) (S3 (catenateB s1 p2) d2 rem2)) of ViewCap d1r' c2 -> Cap (LO p1 (D2 d1l d1r') b2) c2
    DOR ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) d2 rem2)) of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) b2) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Triple (R0 p2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> case uncap (injectRight (cap d1r cl) (S3 (catenateB s1 p2) D0 rem2)) of ViewCap d1r' c2 -> Cap (LO p1 (D2 d1l d1r') b2) c2
    DOR ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) D0 rem2)) of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) b2) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Cap (RY p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> case uncap (injectRight (cap d1r cl) (S3 (catenateB s1 p2) (plugL c d2) rem2)) of ViewCap d1r' c2 -> Cap (LO p1 (D2 d1l d1r') b2) c2
    DOR ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) (plugL c d2) rem2)) of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) b2) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Cap (RO p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> case uncap (injectRight (cap d1r cl) (S3 (catenateB s1 p2) (plugR d2 c) rem2)) of ViewCap d1r' c2 -> Cap (LO p1 (D2 d1l d1r') b2) c2
    DOR ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) (plugR d2 c) rem2)) of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) b2) c2
  where
    -- TODO: uncps
    aux :: Buffer q i l -> HPair (Buffer q) (Buffer q) i l
    aux s2 f = case ejectB s2 of
      H (Shift rem1) s2r1 -> case ejectB rem1 of
        H (Shift rem2) s2r2 -> H rem2 (B2 s2r2 s2r1)
      H (NoShift rem1) s2r1 -> case ejectB rem1 of
        H (Shift rem2) s2r2 -> H rem2 (B2 s2r2 s2r1)
        H (NoShift rem2) s2r2 -> H rem2 (B2 s2r2 s2r1)

    only :: Cap OnlyTriple (Closed Green) q i j -> Cap LeftTriple (Closed Green) q i j
    only (Triple O0{}) = error "Impossible"
    only (Triple (OGG p1 D0 s1)) = Triple (onlyPS p1 s1)
    only (Triple (OGG p1 d1 s1)) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> Triple $ injectWith d1 (S1 rem2) $ (\e -> LG p1 e (B2 s1r2 s1r1))
           H (NoShift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> Triple $ injectWith d1 (S1 rem2) $ (\e -> LG p1 e (B2 s1r2 s1r1))
             H (NoShift rem2) s1r2 -> Triple $ injectWith d1 (S1 rem2) $ (\e -> LG p1 e (B2 s1r2 s1r1))
    only (Cap (OOX p1 d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> foo $ inject (plugR d1 c) (S1 rem2)
               where
                 foo D0 = error "Impossible"
                 foo (D2 lt rt) = case uncap rt of ViewCap rt2 c2 -> Cap (LO p1 (D2 lt rt2) (B2 s1r2 s1r1)) c2
                 foo (DOL ot) = case uncap ot of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) (B2 s1r2 s1r1)) c2
                 foo (DOR ot) = case uncap ot of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) (B2 s1r2 s1r1)) c2
           H (NoShift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> foo $ inject (plugR d1 c) (S1 rem2)
               where
                 foo D0 = error "Impossible"
                 foo (D2 lt rt) = case uncap rt of ViewCap rt2 c2 -> Cap (LO p1 (D2 lt rt2) (B2 s1r2 s1r1)) c2
                 foo (DOL ot) = case uncap ot of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) (B2 s1r2 s1r1)) c2
                 foo (DOR ot) = case uncap ot of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) (B2 s1r2 s1r1)) c2
             H (NoShift rem2) s1r2 -> foo $ inject (plugR d1 c) (S1 rem2)
               where
                 foo D0 = error "Impossible"
                 foo (D2 lt rt) = case uncap rt of ViewCap rt2 c2 -> Cap (LO p1 (D2 lt rt2) (B2 s1r2 s1r1)) c2
                 foo (DOL ot) = case uncap ot of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) (B2 s1r2 s1r1)) c2
                 foo (DOR ot) = case uncap ot of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) (B2 s1r2 s1r1)) c2
    only (Cap (OXO p1@B7{} d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> foo $ inject (plugR d1 c) (S1 rem2)
               where
                 foo D0 = error "Impossible"
                 foo (D2 lt rt) = case uncap lt of ViewCap lt2 c2 -> Cap (LY p1 (D2 lt2 rt) (B2 s1r2 s1r1)) c2
                 foo (DOL ot) = case uncap ot of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
                 foo (DOR ot) = case uncap ot of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
    only (Cap (OXO p1@B8{} d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> Triple (LG p1 (inject (plugR d1 c) (S1 rem2)) (B2 s1r2 s1r1))
    only (Cap (OXO p1@B9{} d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> Triple (LG p1 (inject (plugR d1 c) (S1 rem2)) (B2 s1r2 s1r1))
    only (Cap (OYX p1 d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case plugL c d1 of
               D2 lt rt -> injectRight rt (S1 rem2) $ \e -> case uncap lt of ViewCap lt2 c2 -> Cap (LY p1 (D2 lt2 e) (B2 s1r2 s1r1)) c2
               DOL ot -> case uncap (injectOnly ot (S1 rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
           H (NoShift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case plugL c d1 of
               D2 lt rt -> injectRight rt (S1 rem2) $ \e -> case uncap lt of ViewCap lt2 c2 -> Cap (LY p1 (D2 lt2 e) (B2 s1r2 s1r1)) c2
               DOL ot -> case uncap (injectOnly ot (S1 rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
             H (NoShift rem2) s1r2 -> case plugL c d1 of
               D2 lt rt -> injectRight rt (S1 rem2) $ \e -> case uncap lt of ViewCap lt2 c2 -> Cap (LY p1 (D2 lt2 e) (B2 s1r2 s1r1)) c2
               DOL ot -> case uncap (injectOnly ot (S1 rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
    only (Cap (OGY p1 d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case plugL c d1 of
               D2 lt rt -> injectRight rt (S1 rem2) $ \e -> Triple (LG p1 (D2 lt e) (B2 s1r2 s1r1))
               DOL ot -> Triple (LG p1 (DOL (injectOnly ot (S1 rem2))) (B2 s1r2 s1r1))
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"

    onlyPS :: Buffer F F F F F F F a8 a9 q j k -> Buffer F F F F F F F b8 b9 q i j -> LeftTriple (Closed Green) q i k
    onlyPS p1 s1@B9{} = case popB s1 of
        H s1l1 (Shift rem1) -> case popB rem1 of
          H s1l2 (Shift rem2) -> case popB rem2 of
            H s1l3 (Shift rem3) -> case ejectB rem3 of
              H (Shift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = injectB (injectB (injectB p1 s1l1) s1l2) s1l3
                    s2 = B2 s1r2 s1r1
        H s1l1 (NoShift rem1) -> case popB rem1 of
          H s1l2 (Shift rem2) -> case popB rem2 of
            H s1l3 (Shift rem3) -> case ejectB rem3 of
              H (Shift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
          H s1l2 (NoShift rem2) -> case popB rem2 of
            H s1l3 (Shift rem3) -> case ejectB rem3 of
              H (Shift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
            H s1l3 (NoShift rem3) -> case ejectB rem3 of
              H (Shift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
              H (NoShift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
                H (NoShift rem5) s1r2 -> LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
    onlyPS p1 s1 = case ejectB s1 of
      H (Shift rem1) s1r1 -> case ejectB rem1 of
        H (Shift rem2) s1r2 -> LG (catenateB p1 rem2) D0 (B2 s1r2 s1r1)
      H (NoShift rem1) s1r1 -> case ejectB rem1 of
        H (Shift rem2) s1r2 -> LG (catenateB p1 rem2) D0 (B2 s1r2 s1r1)
        H (NoShift rem2) s1r2 -> LG (catenateB p1 rem2) D0 (B2 s1r2 s1r1)

fixLeft' :: Deque q i j -> Cap LeftTriple q i j
fixLeft' d = case d of
  D0 -> error "Impossible"
  DOL c -> only c
  DOR c -> only c
  (D2 (Triple (LG p1 D0 s1)) (Triple (R0 p2 s2@B9{}))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  (D2 (Triple (LG p1 D0 s1)) (Triple (R0 p2 s2@B8{}))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  (D2 (Triple (LG p1 D0 s1)) (Triple (R0 p2 s2))) -> only (Triple (O0 (catenateB (catenateB (catenateB p1 s1) p2) s2)))
  (D2 (Triple (LG p1 D0 s1)) (Triple (RG p2 d2 s2))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) d2 s2))
  (D2 (Triple (LG p1 D0 s1)) (Triple (RR p2 d2 s2))) -> only (Triple (OXR (catenateB (catenateB p1 s1) p2) d2 s2))
  (D2 (Triple (LG p1 D0 s1)) (Cap (RO p2 d2 s2) c)) -> only (Cap (OXO (catenateB (catenateB p1 s1) p2) d2 s2) c)
  (D2 (Triple (LG p1 D0 s1)) (Cap (RY p2 d2 s2) c)) -> only (Cap (OGY (catenateB (catenateB p1 s1) p2) d2 s2) c)
  (D2 (Triple (L0 p1 s1)) (Triple (R0 p2 s2@B9{}))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  (D2 (Triple (L0 p1 s1)) (Triple (R0 p2 s2@B8{}))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  (D2 (Triple (L0 p1 s1)) (Triple (R0 p2 s2))) -> only (Triple (O0 (catenateB (catenateB (catenateB p1 s1) p2) s2)))
  (D2 (Triple (L0 p1 s1)) (Triple (RG p2 d2 s2))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) d2 s2))
  (D2 (Triple (L0 p1 s1)) (Triple (RR p2 d2 s2))) -> only (Triple (OXR (catenateB (catenateB p1 s1) p2) d2 s2))
  (D2 (Triple (L0 p1 s1)) (Cap (RO p2 d2 s2) c)) -> only (Cap (OXO (catenateB (catenateB p1 s1) p2) d2 s2) c)
  (D2 (Triple (L0 p1 s1)) (Cap (RY p2 d2 s2) c)) -> only (Cap (OGY (catenateB (catenateB p1 s1) p2) d2 s2) c)
  (D2 (Triple (LG p1 d1 s1)) (Triple (RG p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ injectWith d1 (S3 (catenateB s1 p2) d2 rem2) $ (\e -> LG p1 e (B2 s2r2 s2r1))
  (D2 (Triple (LG p1 d1 s1)) (Triple (RR p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ injectWith d1 (S3 (catenateB s1 p2) d2 rem2) $ (\e -> LG p1 e (B2 s2r2 s2r1))
  (D2 (Triple (LG p1 d1 s1)) (Triple (R0 p2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ injectWith d1 (S3 (catenateB s1 p2) D0 rem2) $ (\e -> LG p1 e (B2 s2r2 s2r1))
  (D2 (Triple (LG p1 d1 s1)) (Cap (RY p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ injectWith d1 (S3 (catenateB s1 p2) (plugL c d2) rem2) $ (\e -> LG p1 e (B2 s2r2 s2r1))
  (D2 (Triple (LG p1 d1 s1)) (Cap (RO p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ injectWith d1 (S3 (catenateB s1 p2) (plugR d2 c) rem2) $ (\e -> LG p1 e (B2 s2r2 s2r1))
  (D2 (Triple (LR p1 d1 s1)) (Triple (RG p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ LR p1 (inject d1 (S3 (catenateB s1 p2) d2 rem2)) (B2 s2r2 s2r1)
  (D2 (Triple (LR p1 d1 s1)) (Triple (RR p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ LR p1 (inject d1 (S3 (catenateB s1 p2) d2 rem2)) (B2 s2r2 s2r1)
  (D2 (Triple (LR p1 d1 s1)) (Triple (R0 p2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ LR p1 (inject d1 (S3 (catenateB s1 p2) D0 rem2)) (B2 s2r2 s2r1)
  (D2 (Triple (LR p1 d1 s1)) (Cap (RY p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ LR p1 (inject d1 (S3 (catenateB s1 p2) (plugL c d2) rem2)) (B2 s2r2 s2r1)
  (D2 (Triple (LR p1 d1 s1)) (Cap (RO p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ LR p1 (inject d1 (S3 (catenateB s1 p2) (plugR d2 c) rem2)) (B2 s2r2 s2r1)
  (D2 (Cap (LY p1 d1 s1) cl) (Triple (RG p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight d1r (S3 (catenateB s1 p2) d2 rem2) $ (\e -> f $ Cap (LY p1 (D2 d1l e) (B2 s2r2 s2r1)) cl)
    DOL ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) d2 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LY p1 d1 s1) cl) (Triple (RR p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight d1r (S3 (catenateB s1 p2) d2 rem2) $ (\e -> f $ Cap (LY p1 (D2 d1l e) (B2 s2r2 s2r1)) cl)
    DOL ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) d2 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LY p1 d1 s1) cl) (Triple (R0 p2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight d1r (S3 (catenateB s1 p2) D0 rem2) $ (\e -> f $ Cap (LY p1 (D2 d1l e) (B2 s2r2 s2r1)) cl)
    DOL ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) D0 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LY p1 d1 s1) cl) (Cap (RY p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight d1r (S3 (catenateB s1 p2) (plugL c d2) rem2) $ (\e -> f $ Cap (LY p1 (D2 d1l e) (B2 s2r2 s2r1)) cl)
    DOL ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) (plugL c d2) rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LY p1 d1 s1) cl) (Cap (RO p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight d1r (S3 (catenateB s1 p2) (plugR d2 c) rem2) $ (\e -> f $ Cap (LY p1 (D2 d1l e) (B2 s2r2 s2r1)) cl)
    DOL ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) (plugR d2 c) rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Triple (RG p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight (cap d1r cl) (S3 (catenateB s1 p2) d2 rem2) $ \e -> case uncap e of ViewCap d1r' c2 -> f $ Cap (LO p1 (D2 d1l d1r') (B2 s2r2 s2r1)) c2
    DOR ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) d2 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LO p1 (DOR ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Triple (RR p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight (cap d1r cl) (S3 (catenateB s1 p2) d2 rem2) $ \e -> case uncap e of ViewCap d1r' c2 -> f $ Cap (LO p1 (D2 d1l d1r') (B2 s2r2 s2r1)) c2
    DOR ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) d2 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LO p1 (DOR ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Triple (R0 p2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight (cap d1r cl) (S3 (catenateB s1 p2) D0 rem2) $ \e -> case uncap e of ViewCap d1r' c2 -> f $ Cap (LO p1 (D2 d1l d1r') (B2 s2r2 s2r1)) c2
    DOR ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) D0 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LO p1 (DOR ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Cap (RY p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight (cap d1r cl) (S3 (catenateB s1 p2) (plugL c d2) rem2) $ \e -> case uncap e of ViewCap d1r' c2 -> f $ Cap (LO p1 (D2 d1l d1r') (B2 s2r2 s2r1)) c2
    DOR ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) (plugL c d2) rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LO p1 (DOR ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Cap (RO p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight (cap d1r cl) (S3 (catenateB s1 p2) (plugR d2 c) rem2) $ \e -> case uncap e of ViewCap d1r' c2 -> f $ Cap (LO p1 (D2 d1l d1r') (B2 s2r2 s2r1)) c2
    DOR ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) (plugR d2 c) rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LO p1 (DOR ot2) (B2 s2r2 s2r1)) c2
  where
    aux :: Buffer F F F F c5 c6 c7 c8 c9 q i l -> (forall k3 k4 k5 k6 k7 k8 k9 j' k. Buffer F F k3 k4 k5 k6 k7 k8 k9 q k l -> q j' k-> q i j' -> h) -> h
    aux s2 h = case ejectB s2 of
      H (Shift rem1) s2r1 -> case ejectB rem1 of
        H (Shift rem2) s2r2 -> h rem2 s2r2 s2r1
      H (NoShift rem1) s2r1 -> case ejectB rem1 of
        H (Shift rem2) s2r2 -> h rem2 s2r2 s2r1
        H (NoShift rem2) s2r2 -> h rem2 s2r2 s2r1

    only :: Cap OnlyTriple (Closed cl'') q i j -> g
    only (Triple O0{}) = error "Impossible"
    only (Triple (OGG p1 D0 s1)) = onlyPS p1 s1
    only (Triple (ORX p1 D0 s1)) = onlyPS p1 s1
    only (Triple (OXR p1 D0 s1)) = onlyPS p1 s1
    only (Triple (OGG p1 d1 s1)) = f $ case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> Triple $ injectWith d1 (S1 rem2) $ (\e -> LG p1 e (B2 s1r2 s1r1))
           H (NoShift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> Triple $ injectWith d1 (S1 rem2) $ (\e -> LG p1 e (B2 s1r2 s1r1))
             H (NoShift rem2) s1r2 -> Triple $ injectWith d1 (S1 rem2) $ (\e -> LG p1 e (B2 s1r2 s1r1))
    only (Triple (ORX p1 d1 s1)) = f $ case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> Triple $ LR p1 (inject d1 (S1 rem2)) (B2 s1r2 s1r1)
           H (NoShift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> Triple $ LR p1 (inject d1 (S1 rem2)) (B2 s1r2 s1r1)
             H (NoShift rem2) s1r2 -> Triple $ LR p1 (inject d1 (S1 rem2)) (B2 s1r2 s1r1)
    only (Triple (OXR p1@B6{} d1 s1)) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case inject d1 (S1 rem2) of
                 D0 -> error "Impossible"
                 (D2 lt rt) -> case uncap rt of ViewCap rt2 c2 -> f $ Cap (LO p1 (D2 lt rt2) (B2 s1r2 s1r1)) c2
                 (DOL ot) -> case uncap ot of ViewCap ot2 c2 -> f $ Cap (LO p1 (DOR ot2) (B2 s1r2 s1r1)) c2
                 (DOR ot) -> case uncap ot of ViewCap ot2 c2 -> f $ Cap (LO p1 (DOR ot2) (B2 s1r2 s1r1)) c2
    only (Triple (OXR p1@B7{} d1 s1)) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> injectWith d1 (S1 rem2) $ \foo -> case foo of
                 D0 -> error "Impossible"
                 (D2 lt rt) -> case uncap lt of ViewCap lt2 c2 -> f $ Cap (LY p1 (D2 lt2 rt) (B2 s1r2 s1r1)) c2
                 (DOL ot) -> case uncap ot of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
                 (DOR ot) -> case uncap ot of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
    only (Triple (OXR p1@B8{} d1 s1)) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> injectWith d1 (S1 rem2) $ \e -> f $ Triple (LG p1 e (B2 s1r2 s1r1))
    only (Triple (OXR p1@B9{} d1 s1)) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> injectWith d1 (S1 rem2) $ \e -> f $ Triple (LG p1 e (B2 s1r2 s1r1))

    only (Cap (OOX p1 d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case (plugR d1 c) of -- (S1 rem2) foo
               D2 lt rt -> injectRight rt (S1 rem2) $ \rt2 -> case uncap rt2 of ViewCap rt3 c3 -> f $ Cap (LO p1 (D2 lt rt3) (B2 s1r2 s1r1)) c3
               DOL ot -> injectOnly ot (S1 rem2) $ \ot2 -> case uncap ot2 of ViewCap ot3 c3 -> f $ Cap (LO p1 (DOR ot3) (B2 s1r2 s1r1)) c3
               DOR ot -> injectOnly ot (S1 rem2) $ \ot2 -> case uncap ot2 of ViewCap ot3 c3 -> f $ Cap (LO p1 (DOR ot3) (B2 s1r2 s1r1)) c3
               D0 -> error "Impossible"
           H (NoShift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case (plugR d1 c) of -- (S1 rem2) foo
               D2 lt rt -> injectRight rt (S1 rem2) $ \rt2 -> case uncap rt2 of ViewCap rt3 c3 -> f $ Cap (LO p1 (D2 lt rt3) (B2 s1r2 s1r1)) c3
               DOL ot -> injectOnly ot (S1 rem2) $ \ot2 -> case uncap ot2 of ViewCap ot3 c3 -> f $ Cap (LO p1 (DOR ot3) (B2 s1r2 s1r1)) c3
               DOR ot -> injectOnly ot (S1 rem2) $ \ot2 -> case uncap ot2 of ViewCap ot3 c3 -> f $ Cap (LO p1 (DOR ot3) (B2 s1r2 s1r1)) c3
               D0 -> error "Impossible"
             H (NoShift rem2) s1r2 -> case (plugR d1 c) of -- (S1 rem2) foo
               D2 lt rt -> injectRight rt (S1 rem2) $ \rt2 -> case uncap rt2 of ViewCap rt3 c3 -> f $ Cap (LO p1 (D2 lt rt3) (B2 s1r2 s1r1)) c3
               DOL ot -> injectOnly ot (S1 rem2) $ \ot2 -> case uncap ot2 of ViewCap ot3 c3 -> f $ Cap (LO p1 (DOR ot3) (B2 s1r2 s1r1)) c3
               DOR ot -> injectOnly ot (S1 rem2) $ \ot2 -> case uncap ot2 of ViewCap ot3 c3 -> f $ Cap (LO p1 (DOR ot3) (B2 s1r2 s1r1)) c3
               D0 -> error "Impossible"
    only (Cap (OXO p1@B7{} d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> injectWith (plugR d1 c) (S1 rem2) $ \foo -> case foo of
                 D0 -> error "Impossible"
                 (D2 lt rt) -> case uncap lt of ViewCap lt2 c2 -> f $ Cap (LY p1 (D2 lt2 rt) (B2 s1r2 s1r1)) c2
                 (DOL ot) -> case uncap ot of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
                 (DOR ot) -> case uncap ot of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
    only (Cap (OXO p1@B8{} d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> injectWith (plugR d1 c) (S1 rem2) $ \e -> f $ Triple (LG p1 e (B2 s1r2 s1r1))
    only (Cap (OXO p1@B9{} d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> injectWith (plugR d1 c) (S1 rem2) $ \e -> f $ Triple (LG p1 e (B2 s1r2 s1r1))
    only (Cap (OYX p1 d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case plugL c d1 of
               D2 lt rt -> injectRight rt (S1 rem2) $ \e -> case uncap lt of ViewCap lt2 c2 -> f $ Cap (LY p1 (D2 lt2 e) (B2 s1r2 s1r1)) c2
               DOL ot -> injectOnly ot (S1 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
           H (NoShift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case plugL c d1 of
               D2 lt rt -> injectRight rt (S1 rem2) $ \e -> case uncap lt of ViewCap lt2 c2 -> f $ Cap (LY p1 (D2 lt2 e) (B2 s1r2 s1r1)) c2
               DOL ot -> injectOnly ot (S1 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
             H (NoShift rem2) s1r2 -> case plugL c d1 of
               D2 lt rt -> injectRight rt (S1 rem2) $ \e -> case uncap lt of ViewCap lt2 c2 -> f $ Cap (LY p1 (D2 lt2 e) (B2 s1r2 s1r1)) c2
               DOL ot -> injectOnly ot (S1 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
    only (Cap (OGY p1 d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case plugL c d1 of
               D2 lt rt -> injectRight rt (S1 rem2) $ \e -> f $ Triple (LG p1 (D2 lt e) (B2 s1r2 s1r1))
               DOL ot -> injectOnly ot (S1 rem2) $ \e -> f $ Triple (LG p1 (DOL e) (B2 s1r2 s1r1))
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"

    onlyPS :: Buffer F F F F a5 a6 a7 a8 a9 q j' j -> Buffer F F F F b5 b6 b7 b8 b9 q i j' -> g -- LeftTriple (Closed Green) q i k
    onlyPS p1 s1@B9{} = case popB s1 of
        H s1l1 (Shift rem1) -> case popB rem1 of
          H s1l2 (Shift rem2) -> case popB rem2 of
            H s1l3 (Shift rem3) -> case ejectB rem3 of
              H (Shift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> f $ Triple $ LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = injectB (injectB (injectB p1 s1l1) s1l2) s1l3
                    s2 = B2 s1r2 s1r1
        H s1l1 (NoShift rem1) -> case popB rem1 of
          H s1l2 (Shift rem2) -> case popB rem2 of
            H s1l3 (Shift rem3) -> case ejectB rem3 of
              H (Shift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> f $ Triple $ LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
          H s1l2 (NoShift rem2) -> case popB rem2 of
            H s1l3 (Shift rem3) -> case ejectB rem3 of
              H (Shift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> f $ Triple $ LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
            H s1l3 (NoShift rem3) -> case ejectB rem3 of
              H (Shift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> f $ Triple $ LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
              H (NoShift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> f $ Triple $ LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
                H (NoShift rem5) s1r2 -> f $ Triple $ LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
    onlyPS p1 s1 = case ejectB s1 of
      H (Shift rem1) s1r1 -> case ejectB rem1 of
        H (Shift rem2) s1r2 -> f $ Triple $ LG (catenateB p1 rem2) D0 (B2 s1r2 s1r1)
      H (NoShift rem1) s1r1 -> case ejectB rem1 of
        H (Shift rem2) s1r2 -> f $ Triple $ LG (catenateB p1 rem2) D0 (B2 s1r2 s1r1)
        H (NoShift rem2) s1r2 -> f $ Triple $ LG (catenateB p1 rem2) D0 (B2 s1r2 s1r1)


fixRight :: Deque (Closed Green) (Closed Green) q i j -> Cap RightTriple (Closed Green) q i j
fixRight d = case d of
  D0 -> error "Impossible"
  (DOL c) -> only c
  (DOR c) -> only c
  (D2 (Triple (L0 p2@B9{} s2)) (Triple (RG p1 D0 s1))) -> only (Triple (OGG p2 D0 (catenateB s2 (catenateB p1 s1))))
  (D2 (Triple (L0 p2@B8{} s2)) (Triple (RG p1 D0 s1))) -> only (Triple (OGG p2 D0 (catenateB s2 (catenateB p1 s1))))
  (D2 (Triple (L0 p2 s2))      (Triple (RG p1 D0 s1))) -> only (Triple (O0 (catenateB p2 (catenateB s2 (catenateB p1 s1)))))
  (D2 (Triple (LG p2 d2 s2))    (Triple (RG p1 D0 s1))) -> only (Triple (OGG p2 d2 (catenateB s2 (catenateB p1 s1))))
  (D2 (Cap (LO p2 d2 s2) c)     (Triple (RG p1 D0 s1))) -> only (Cap (OOX p2 d2 (catenateB (catenateB s2 p1) s1)) c)
  (D2 (Cap (LY p2 d2 s2) c)     (Triple (RG p1 D0 s1))) -> only (Cap (OYX p2 d2 (catenateB (catenateB s2 p1) s1)) c)
  (D2 (Triple (L0 p2@B9{} s2)) (Triple (R0 p1 s1))) -> only (Triple (OGG p2 D0 (catenateB s2 (catenateB p1 s1))))
  (D2 (Triple (L0 p2@B8{} s2)) (Triple (R0 p1 s1))) -> only (Triple (OGG p2 D0 (catenateB s2 (catenateB p1 s1))))
  (D2 (Triple (L0 p2 s2))      (Triple (R0 p1 s1))) -> only (Triple (O0 (catenateB p2 (catenateB s2 (catenateB p1 s1)))))
  (D2 (Triple (LG p2 d2 s2))    (Triple (R0 p1 s1))) -> only (Triple (OGG p2 d2 (catenateB s2 (catenateB p1 s1))))
  (D2 (Cap (LO p2 d2 s2) c)     (Triple (R0 p1 s1))) -> only (Cap (OOX p2 d2 (catenateB (catenateB s2 p1) s1)) c)
  (D2 (Cap (LY p2 d2 s2) c)     (Triple (R0 p1 s1))) -> only (Cap (OYX p2 d2 (catenateB (catenateB s2 p1) s1)) c)
  (D2 (Triple (LG p2 d2 s2)) (Triple (RG p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> Triple $ pushWith (S3 rem2 d2 (catenateB s2 p1)) d1 $ \e -> RG (B2 p2l1 p2l2) e s1
  (D2 (Triple (L0 p2 s2))    (Triple (RG p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> Triple $ pushWith (S3 rem2 D0 (catenateB s2 p1))           d1 $ \e -> RG (B2 p2l1 p2l2) e s1
  (D2 (Cap (LY p2 d2 s2) c)  (Triple (RG p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> Triple $ pushWith (S3 rem2 (plugL c d2) (catenateB s2 p1)) d1 $ \e -> RG (B2 p2l1 p2l2) e s1
  (D2 (Cap (LO p2 d2 s2) c)  (Triple (RG p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> Triple $ pushWith (S3 rem2 (plugR d2 c) (catenateB s2 p1)) d1 $ \e -> RG (B2 p2l1 p2l2) e s1
  (D2 (Triple (LG p2 d2 s2)) (Cap (RO p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> Cap (RO (B2 p2l1 p2l2) (D2 (pushLeftG (S3 rem2 d2 (catenateB s2 p1)) d1l) d1r) s1) cl
    DOR ot -> case uncap (pushOnly (S3 rem2 d2 (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RO (B2 p2l1 p2l2) (DOR ot2) s1) c2
  (D2 (Triple (L0 p2 s2)) (Cap (RO p1 d1 s1) cl)) ->    aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> Cap (RO (B2 p2l1 p2l2) (D2 (pushLeftG (S3 rem2 D0 (catenateB s2 p1)) d1l) d1r) s1) cl
    DOR ot -> case uncap (pushOnly (S3 rem2 D0 (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RO (B2 p2l1 p2l2) (DOR ot2) s1) c2
  (D2 (Cap (LY p2 d2 s2) cr) (Cap (RO p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> Cap (RO (B2 p2l1 p2l2) (D2 (pushLeftG (S3 rem2 (plugL cr d2) (catenateB s2 p1)) d1l) d1r) s1) cl
    DOR ot -> case uncap (pushOnly (S3 rem2 (plugL cr d2) (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RO (B2 p2l1 p2l2) (DOR ot2) s1) c2
  (D2 (Cap (LO p2 d2 s2) cr) (Cap (RO p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> Cap (RO (B2 p2l1 p2l2) (D2 (pushLeftG (S3 rem2 (plugR d2 cr) (catenateB s2 p1)) d1l) d1r) s1) cl
    DOR ot -> case uncap (pushOnly (S3 rem2 (plugR d2 cr) (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RO (B2 p2l1 p2l2) (DOR ot2) s1) c2
  (D2 (Triple (LG p2 d2 s2)) (Cap (RY p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> case uncap (pushLeftG (S3 rem2 d2 (catenateB s2 p1)) (cap d1l cl)) of ViewCap d1l' c2 -> Cap (RY (B2 p2l1 p2l2) (D2 d1l' d1r) s1) c2
    DOL ot -> case uncap (pushOnly (S3 rem2 d2 (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RY (B2 p2l1 p2l2) (DOL ot2) s1) c2
  (D2 (Triple (L0 p2 s2)) (Cap (RY p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> case uncap (pushLeftG (S3 rem2 D0 (catenateB s2 p1)) (cap d1l cl)) of ViewCap d1l' c2 -> Cap (RY (B2 p2l1 p2l2) (D2 d1l' d1r) s1) c2
    DOL ot -> case uncap (pushOnly (S3 rem2 D0 (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RY (B2 p2l1 p2l2) (DOL ot2) s1) c2
  (D2 (Cap (LY p2 d2 s2) cr) (Cap (RY p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> case uncap (pushLeftG (S3 rem2 (plugL cr d2) (catenateB s2 p1)) (cap d1l cl)) of ViewCap d1l' c2 -> Cap (RY (B2 p2l1 p2l2) (D2 d1l' d1r) s1) c2
    DOL ot -> case uncap (pushOnly (S3 rem2 (plugL cr d2) (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RY (B2 p2l1 p2l2) (DOL ot2) s1) c2
  (D2 (Cap (LO p2 d2 s2) cr) (Cap (RY p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> case uncap (pushLeftG (S3 rem2 (plugR d2 cr) (catenateB s2 p1)) (cap d1l cl)) of ViewCap d1l' c2 -> Cap (RY (B2 p2l1 p2l2) (D2 d1l' d1r) s1) c2
    DOL ot -> case uncap (pushOnly (S3 rem2 (plugR d2 cr) (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RY (B2 p2l1 p2l2) (DOL ot2) s1) c2
  where
    aux :: Buffer F F F F c5 c6 c7 c8 c9 q i l -> (forall k3 k4 k5 k6 k7 k8 k9 j k. q k l -> q j k-> Buffer F F k3 k4 k5 k6 k7 k8 k9 q i j -> g) -> g
    aux p1 f = case popB p1 of
      H p1l1 (Shift rem1) -> case popB rem1 of
        H p1l2 (Shift rem2) -> f p1l1 p1l2 rem2
      H p1l1 (NoShift rem1) -> case popB rem1 of
        H p1l2 (Shift rem2) -> f p1l1 p1l2 rem2
        H p1l2 (NoShift rem2) -> f p1l1 p1l2 rem2

    only :: Cap OnlyTriple (Closed Green) q i j -> Cap RightTriple (Closed Green) q i j
    only (Triple O0{}) = error "Impossible"
    only (Triple (OGG p1 D0 s1)) = Triple (onlyPS p1 s1)
    only (Triple (OGG p1 d1 s1)) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> Triple $ pushWith (S1 rem2) d1 $ \e -> RG (B2 p1l1 p1l2) e s1
           H p1l1 (NoShift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> Triple $ pushWith (S1 rem2) d1 $ \e -> RG (B2 p1l1 p1l2) e s1
             H p1l2 (NoShift rem2) -> Triple $ pushWith (S1 rem2) d1 $ \e -> RG (B2 p1l1 p1l2) e s1
    only (Cap (OOX p1 d1 s1@B6{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> foo $ push (S1 rem2) (plugR d1 c)
               where
                 foo (D2 lt rt) = case uncap rt of ViewCap rt2 c2 -> Cap (RO (B2 p1l1 p1l2) (D2 lt rt2) s1) c2
                 foo (DOL ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 foo (DOR ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 foo D0 = error "Impossible"
    only (Cap (OOX p1 d1 s1@B7{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> foo $ push (S1 rem2) (plugR d1 c)
               where
                 foo (D2 lt rt) = case uncap lt of ViewCap lt2 c2 -> Cap (RY (B2 p1l1 p1l2) (D2 lt2 rt) s1) c2
                 foo (DOL ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
                 foo (DOR ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
                 foo D0 = error "Impossible"
    only (Cap (OOX p1 d1 s1@B8{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> Triple (RG (B2 p1l1 p1l2) (push (S1 rem2) (plugR d1 c)) s1)
    only (Cap (OOX p1 d1 s1@B9{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> Triple (RG (B2 p1l1 p1l2) (push (S1 rem2) (plugR d1 c)) s1)
    only (Cap (OXO p1 d1 s1) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> foo $ push (S1 rem2) (plugR d1 c)
               where
                 foo (D2 lt rt) = case uncap rt of ViewCap rt2 c2 -> Cap (RO (B2 p1l1 p1l2) (D2 lt rt2) s1) c2
                 foo (DOL ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 foo (DOR ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 foo D0 = error "Impossible"
           H p1l1 (NoShift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> foo $ push (S1 rem2) (plugR d1 c)
               where
                 foo (D2 lt rt) = case uncap rt of ViewCap rt2 c2 -> Cap (RO (B2 p1l1 p1l2) (D2 lt rt2) s1) c2
                 foo (DOL ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 foo (DOR ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 foo D0 = error "Impossible"
             H p1l2 (NoShift rem2) -> foo $ push (S1 rem2) (plugR d1 c)
               where
                 foo (D2 lt rt) = case uncap rt of ViewCap rt2 c2 -> Cap (RO (B2 p1l1 p1l2) (D2 lt rt2) s1) c2
                 foo (DOL ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 foo (DOR ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 foo D0 = error "Impossible"
    only (Cap (OYX p1 d1 s1@B7{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case plugL c d1 of
               D2 lt rt -> case uncap (pushLeftG (S1 rem2) lt) of ViewCap lt2 c2 -> Cap (RY (B2 p1l1 p1l2) (D2 lt2 rt) s1) c2
               DOL ot -> case uncap (pushOnly (S1 rem2) ot) of ViewCap ot2 c2 -> Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
    only (Cap (OYX p1 d1 s1@B8{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> pushWith (S1 rem2) (plugL c d1) $ \e -> Triple (RG (B2 p1l1 p1l2) e s1)
    only (Cap (OYX p1 d1 s1@B9{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> pushWith (S1 rem2) (plugL c d1) $ \e -> Triple (RG (B2 p1l1 p1l2) e s1)
    only (Cap (OGY p1 d1 s1) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case plugL c d1 of
               D2 lt rt -> case uncap (pushLeftG (S1 rem2) lt) of ViewCap lt2 c2 -> Cap (RY (B2 p1l1 p1l2) (D2 lt2 rt) s1) c2
               DOL ot -> case uncap (pushOnly (S1 rem2) ot) of ViewCap ot2 c2 -> Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
           H p1l1 (NoShift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case plugL c d1 of
               D2 lt rt -> case uncap (pushLeftG (S1 rem2) lt) of ViewCap lt2 c2 -> Cap (RY (B2 p1l1 p1l2) (D2 lt2 rt) s1) c2
               DOL ot -> case uncap (pushOnly (S1 rem2) ot) of ViewCap ot2 c2 -> Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
             H p1l2 (NoShift rem2) -> case plugL c d1 of
               D2 lt rt -> case uncap (pushLeftG (S1 rem2) lt) of ViewCap lt2 c2 -> Cap (RY (B2 p1l1 p1l2) (D2 lt2 rt) s1) c2
               DOL ot -> case uncap (pushOnly (S1 rem2) ot) of ViewCap ot2 c2 -> Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"

    onlyPS :: Buffer F F F F F F F a8 a9 q j k -> Buffer F F F F F F F b8 b9 q i j -> RightTriple (Closed Green) q i k
    onlyPS p1@B9{} s1 = case ejectB p1 of
        H (Shift rem1) p1r1 -> case ejectB rem1 of
          H (Shift rem2) p1r2 -> case ejectB rem2 of
            H (Shift rem3) p1r3 -> case popB rem3 of
              H p1l1 (Shift rem4) -> case popB rem4 of
                H p1l2 (Shift rem5) -> RG p2 (push (S1 rem5) D0) s2
                  where
                    p2 = B2 p1l1 p1l2
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
        H (NoShift rem1) p1r1 -> case ejectB rem1 of
          H (Shift rem2) p1r2 -> case ejectB rem2 of
            H (Shift rem3) p1r3 -> case popB rem3 of
              H p1l1 (Shift rem4) -> case popB rem4 of
                H p1l2 (Shift rem5) -> RG p2 (push (S1 rem5) D0) s2
                  where
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
                    p2 = B2 p1l1 p1l2
          H (NoShift rem2) p1r2 -> case ejectB rem2 of
            H (Shift rem3) p1r3 -> case popB rem3 of
              H p1l1 (Shift rem4) -> case popB rem4 of
                H p1l2 (Shift rem5) -> RG p2 (push (S1 rem5) D0) s2
                  where
                    p2 = B2 p1l1 p1l2
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
            H (NoShift rem3) p1r3 -> case popB rem3 of
              H p1l1 (Shift rem4) -> case popB rem4 of
                H p1l2 (Shift rem5) -> RG p2 (push (S1 rem5) D0) s2
                  where
                    p2 = B2 p1l1 p1l2
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
              H p1l1 (NoShift rem4) -> case popB rem4 of
                H p1l2 (Shift rem5) -> RG p2 (push (S1 rem5) D0) s2
                  where
                    p2 = B2 p1l1 p1l2
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
                H p1l2 (NoShift rem5) -> RG p2 (push (S1 rem5) D0) s2
                  where
                    p2 = B2 p1l1 p1l2
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
    onlyPS p1 s1 = case popB p1 of
      H p1l1 (Shift rem1) -> case popB rem1 of
        H p1l2 (Shift rem2) -> RG (B2 p1l1 p1l2) D0 (catenateB rem2 s1)
      H p1l1 (NoShift rem1) -> case popB rem1 of
        H p1l2 (Shift rem2) -> RG (B2 p1l1 p1l2) D0 (catenateB rem2 s1)
        H p1l2 (NoShift rem2) -> RG (B2 p1l1 p1l2) D0 (catenateB rem2 s1)

fixRight' :: forall cl cr q i j g. Deque (Closed cl) (Closed cr) q i j -> (forall cr'. Cap RightTriple (Closed cr') q i j -> g) -> g
fixRight' d f = case d of
  D0 -> error "Impossible"
  (DOL c) -> only c
  (DOR c) -> only c
  (D2 (Triple (L0 p2@B9{} s2)) (Triple (RG p1 D0 s1))) -> only (Triple (OGG p2 D0 (catenateB s2 (catenateB p1 s1))))
  (D2 (Triple (L0 p2@B8{} s2)) (Triple (RG p1 D0 s1))) -> only (Triple (OGG p2 D0 (catenateB s2 (catenateB p1 s1))))
  (D2 (Triple (L0 p2 s2))      (Triple (RG p1 D0 s1))) -> only (Triple (O0 (catenateB p2 (catenateB s2 (catenateB p1 s1)))))
  (D2 (Triple (LG p2 d2 s2))    (Triple (RG p1 D0 s1))) -> only (Triple (OGG p2 d2 (catenateB s2 (catenateB p1 s1))))
  (D2 (Triple (LR p2 d2 s2))    (Triple (RG p1 D0 s1))) -> only (Triple (ORX p2 d2 (catenateB s2 (catenateB p1 s1))))
  (D2 (Cap (LO p2 d2 s2) c)     (Triple (RG p1 D0 s1))) -> only (Cap (OOX p2 d2 (catenateB (catenateB s2 p1) s1)) c)
  (D2 (Cap (LY p2 d2 s2) c)     (Triple (RG p1 D0 s1))) -> only (Cap (OYX p2 d2 (catenateB (catenateB s2 p1) s1)) c)
  (D2 (Triple (L0 p2@B9{} s2)) (Triple (R0 p1 s1))) -> only (Triple (OGG p2 D0 (catenateB s2 (catenateB p1 s1))))
  (D2 (Triple (L0 p2@B8{} s2)) (Triple (R0 p1 s1))) -> only (Triple (OGG p2 D0 (catenateB s2 (catenateB p1 s1))))
  (D2 (Triple (L0 p2 s2))      (Triple (R0 p1 s1))) -> only (Triple (O0 (catenateB p2 (catenateB s2 (catenateB p1 s1)))))
  (D2 (Triple (LG p2 d2 s2))    (Triple (R0 p1 s1))) -> only (Triple (OGG p2 d2 (catenateB s2 (catenateB p1 s1))))
  (D2 (Triple (LR p2 d2 s2))    (Triple (R0 p1 s1))) -> only (Triple (ORX p2 d2 (catenateB s2 (catenateB p1 s1))))
  (D2 (Cap (LO p2 d2 s2) c)     (Triple (R0 p1 s1))) -> only (Cap (OOX p2 d2 (catenateB (catenateB s2 p1) s1)) c)
  (D2 (Cap (LY p2 d2 s2) c)     (Triple (R0 p1 s1))) -> only (Cap (OYX p2 d2 (catenateB (catenateB s2 p1) s1)) c)
  (D2 (Triple (LG p2 d2 s2)) (Triple (RG p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> f $ Triple $ pushWith (S3 rem2 d2 (catenateB s2 p1)) d1 $ \e -> RG (B2 p2l1 p2l2) e s1
  (D2 (Triple (LR p2 d2 s2)) (Triple (RG p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> f $ Triple $ pushWith (S3 rem2 d2 (catenateB s2 p1)) d1 $ \e -> RG (B2 p2l1 p2l2) e s1
  (D2 (Triple (L0 p2 s2))    (Triple (RG p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> f $ Triple $ pushWith (S3 rem2 D0 (catenateB s2 p1))           d1 $ \e -> RG (B2 p2l1 p2l2) e s1
  (D2 (Cap (LY p2 d2 s2) c)  (Triple (RG p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> f $ Triple $ pushWith (S3 rem2 (plugL c d2) (catenateB s2 p1)) d1 $ \e -> RG (B2 p2l1 p2l2) e s1
  (D2 (Cap (LO p2 d2 s2) c)  (Triple (RG p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> f $ Triple $ pushWith (S3 rem2 (plugR d2 c) (catenateB s2 p1)) d1 $ \e -> RG (B2 p2l1 p2l2) e s1
  (D2 (Triple (LG p2 d2 s2)) (Triple (RR p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> f $ Triple $ RR (B2 p2l1 p2l2) (push (S3 rem2 d2 (catenateB s2 p1))           d1) s1
  (D2 (Triple (LR p2 d2 s2)) (Triple (RR p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> f $ Triple $ RR (B2 p2l1 p2l2) (push (S3 rem2 d2 (catenateB s2 p1))           d1) s1
  (D2 (Triple (L0 p2 s2))    (Triple (RR p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> f $ Triple $ RR (B2 p2l1 p2l2) (push (S3 rem2 D0 (catenateB s2 p1))           d1) s1
  (D2 (Cap (LY p2 d2 s2) c)  (Triple (RR p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> f $ Triple $ RR (B2 p2l1 p2l2) (push (S3 rem2 (plugL c d2) (catenateB s2 p1)) d1) s1
  (D2 (Cap (LO p2 d2 s2) c)  (Triple (RR p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> f $ Triple $ RR (B2 p2l1 p2l2) (push (S3 rem2 (plugR d2 c) (catenateB s2 p1)) d1) s1
  (D2 (Triple (LG p2 d2 s2)) (Cap (RO p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> f $ Cap (RO (B2 p2l1 p2l2) (D2 (pushLeftG (S3 rem2 d2 (catenateB s2 p1)) d1l) d1r) s1) cl
    DOR ot -> pushOnly (S3 rem2 d2 (catenateB s2 p1)) (cap ot cl) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RO (B2 p2l1 p2l2) (DOR ot2) s1) c2
  (D2 (Triple (LR p2 d2 s2)) (Cap (RO p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> f $ Cap (RO (B2 p2l1 p2l2) (D2 (pushLeftG (S3 rem2 d2 (catenateB s2 p1)) d1l) d1r) s1) cl
    DOR ot -> pushOnly (S3 rem2 d2 (catenateB s2 p1)) (cap ot cl) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RO (B2 p2l1 p2l2) (DOR ot2) s1) c2
  (D2 (Triple (L0 p2 s2)) (Cap (RO p1 d1 s1) cl)) ->    aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> f $ Cap (RO (B2 p2l1 p2l2) (D2 (pushLeftG (S3 rem2 D0 (catenateB s2 p1)) d1l) d1r) s1) cl
    DOR ot -> pushOnly (S3 rem2 D0 (catenateB s2 p1)) (cap ot cl) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RO (B2 p2l1 p2l2) (DOR ot2) s1) c2
  (D2 (Cap (LY p2 d2 s2) cr) (Cap (RO p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> f $ Cap (RO (B2 p2l1 p2l2) (D2 (pushLeftG (S3 rem2 (plugL cr d2) (catenateB s2 p1)) d1l) d1r) s1) cl
    DOR ot -> pushOnly (S3 rem2 (plugL cr d2) (catenateB s2 p1)) (cap ot cl) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RO (B2 p2l1 p2l2) (DOR ot2) s1) c2
  (D2 (Cap (LO p2 d2 s2) cr) (Cap (RO p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> f $ Cap (RO (B2 p2l1 p2l2) (D2 (pushLeftG (S3 rem2 (plugR d2 cr) (catenateB s2 p1)) d1l) d1r) s1) cl
    DOR ot -> pushOnly (S3 rem2 (plugR d2 cr) (catenateB s2 p1)) (cap ot cl) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RO (B2 p2l1 p2l2) (DOR ot2) s1) c2
  (D2 (Triple (LG p2 d2 s2)) (Cap (RY p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> pushLeft (S3 rem2 d2 (catenateB s2 p1)) (cap d1l cl) $ \e -> case uncap e of ViewCap d1l' c2 -> f $ Cap (RY (B2 p2l1 p2l2) (D2 d1l' d1r) s1) c2
    DOL ot -> pushOnly (S3 rem2 d2 (catenateB s2 p1)) (cap ot cl) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RY (B2 p2l1 p2l2) (DOL ot2) s1) c2
  (D2 (Triple (LR p2 d2 s2)) (Cap (RY p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> pushLeft (S3 rem2 d2 (catenateB s2 p1)) (cap d1l cl) $ \e -> case uncap e of ViewCap d1l' c2 -> f $ Cap (RY (B2 p2l1 p2l2) (D2 d1l' d1r) s1) c2
    DOL ot -> pushOnly (S3 rem2 d2 (catenateB s2 p1)) (cap ot cl) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RY (B2 p2l1 p2l2) (DOL ot2) s1) c2
  (D2 (Triple (L0 p2 s2)) (Cap (RY p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> pushLeft (S3 rem2 D0 (catenateB s2 p1)) (cap d1l cl) $ \e -> case uncap e of ViewCap d1l' c2 -> f $ Cap (RY (B2 p2l1 p2l2) (D2 d1l' d1r) s1) c2
    DOL ot -> pushOnly (S3 rem2 D0 (catenateB s2 p1)) (cap ot cl) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RY (B2 p2l1 p2l2) (DOL ot2) s1) c2
  (D2 (Cap (LY p2 d2 s2) cr) (Cap (RY p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> pushLeft (S3 rem2 (plugL cr d2) (catenateB s2 p1)) (cap d1l cl) $ \e -> case uncap e of ViewCap d1l' c2 -> f $ Cap (RY (B2 p2l1 p2l2) (D2 d1l' d1r) s1) c2
    DOL ot -> pushOnly (S3 rem2 (plugL cr d2) (catenateB s2 p1)) (cap ot cl) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RY (B2 p2l1 p2l2) (DOL ot2) s1) c2
  (D2 (Cap (LO p2 d2 s2) cr) (Cap (RY p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> pushLeft (S3 rem2 (plugR d2 cr) (catenateB s2 p1)) (cap d1l cl) $ \e -> case uncap e of ViewCap d1l' c2 -> f $ Cap (RY (B2 p2l1 p2l2) (D2 d1l' d1r) s1) c2
    DOL ot -> pushOnly (S3 rem2 (plugR d2 cr) (catenateB s2 p1)) (cap ot cl) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RY (B2 p2l1 p2l2) (DOL ot2) s1) c2
  where
    aux :: Buffer F F F F c5 c6 c7 c8 c9 q i' j -> (forall k3 k4 k5 k6 k7 k8 k9 j' k. q k j -> q j' k-> Buffer F F k3 k4 k5 k6 k7 k8 k9 q i' j' -> h) -> h
    aux p1 g = case popB p1 of
      H p1l1 (Shift rem1) -> case popB rem1 of
        H p1l2 (Shift rem2) -> g p1l1 p1l2 rem2
      H p1l1 (NoShift rem1) -> case popB rem1 of
        H p1l2 (Shift rem2) -> g p1l1 p1l2 rem2
        H p1l2 (NoShift rem2) -> g p1l1 p1l2 rem2

    only :: Cap OnlyTriple (Closed cr'') q i j -> g
    only (Triple O0{}) = error "Impossible"
    only (Triple (OGG p1 D0 s1)) = onlyPS p1 s1
    only (Triple (ORX p1 D0 s1)) = onlyPS p1 s1
    only (Triple (OXR p1 D0 s1)) = onlyPS p1 s1
    only (Triple (OGG p1 d1 s1)) = f $ case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> Triple $ pushWith (S1 rem2) d1 $ \e -> RG (B2 p1l1 p1l2) e s1
           H p1l1 (NoShift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> Triple $ pushWith (S1 rem2) d1 $ \e -> RG (B2 p1l1 p1l2) e s1
             H p1l2 (NoShift rem2) -> Triple $ pushWith (S1 rem2) d1 $ \e -> RG (B2 p1l1 p1l2) e s1
    only (Triple (ORX p1 d1 s1@B5{})) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case d1 of
                 (D2 lt rt) -> f $ Triple (RR (B2 p1l1 p1l2) (D2 (pushLeftG (S1 rem2) lt) rt) s1)
                 (DOR ot)   -> f $ Triple (RR (B2 p1l1 p1l2) (DOR (pushOnly (S1 rem2) ot)) s1)
                 (DOL ot)   -> f $ Triple (RR (B2 p1l1 p1l2) (DOR (pushOnly (S1 rem2) ot)) s1)
                 D0 -> f $ Triple (RR (B2 p1l1 p1l2) (DOR (Triple (O0 (B1 (S1 rem2))))) s1)
    only (Triple (ORX p1 d1 s1@B6{})) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case d1 of
                 (D2 lt rt) -> case uncap rt of ViewCap rt2 cap2 -> f $ Cap (RO (B2 p1l1 p1l2) (D2 (pushLeftG (S1 rem2) lt) rt2) s1) cap2
                 (DOR ot)   -> pushOnly (S1 rem2) ot $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 (DOL ot)   -> pushOnly (S1 rem2) ot $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 D0 -> f $ Cap (RO (B2 p1l1 p1l2) (DOR Opening) s1) (O0 (B1 (S1 rem2)))
    only (Triple (ORX p1 d1 s1@B7{})) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case d1 of
                 (D2 lt rt) -> case uncap (pushLeftG (S1 rem2) lt) of ViewCap lt2 cap2 -> f $ Cap (RY (B2 p1l1 p1l2) (D2 lt2 rt) s1) cap2
                 (DOR ot)   -> pushOnly (S1 rem2) ot $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
                 (DOL ot)   -> pushOnly (S1 rem2) ot $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
                 D0 -> f $ Cap (RY (B2 p1l1 p1l2) (DOL Opening) s1) (O0 (B1 (S1 rem2)))
    only (Triple (ORX p1 d1 s1@B8{})) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case d1 of
                 (D2 lt rt) -> f $ Triple (RG (B2 p1l1 p1l2) (D2 (pushLeftG (S1 rem2) lt) rt) s1)
                 (DOR ot)   -> pushOnly (S1 rem2) ot $ \ot2 -> f $ Triple (RG (B2 p1l1 p1l2) (DOL ot2) s1)
                 (DOL ot)   -> pushOnly (S1 rem2) ot $ \ot2 -> f $ Triple (RG (B2 p1l1 p1l2) (DOL ot2) s1)
                 D0 -> f $ Triple (RG (B2 p1l1 p1l2) (DOR (Triple (O0 (B1 (S1 rem2))))) s1)
    only (Triple (ORX p1 d1 s1@B9{})) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case d1 of
                 (D2 lt rt) -> f $ Triple (RG (B2 p1l1 p1l2) (D2 (pushLeftG (S1 rem2) lt) rt) s1)
                 (DOR ot)   -> pushOnly (S1 rem2) ot $ \ot2 -> f $ Triple (RG (B2 p1l1 p1l2) (DOL ot2) s1)
                 (DOL ot)   -> pushOnly (S1 rem2) ot $ \ot2 -> f $ Triple (RG (B2 p1l1 p1l2) (DOL ot2) s1)
                 D0 -> f $ Triple (RG (B2 p1l1 p1l2) (DOR (Triple (O0 (B1 (S1 rem2))))) s1)
    only (Cap (OOX p1 d1 s1@B6{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case d1 of
                 (D2 lt rt) -> f $ Cap (RO (B2 p1l1 p1l2) (D2 (pushLeftG (S1 rem2) lt) rt) s1) c
                 (DOR ot)   -> pushOnly (S1 rem2) (cap ot c) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
    only (Cap (OOX p1 d1 s1@B7{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> pushWith (S1 rem2) (plugR d1 c) $ \foo -> case foo of
               (D2 lt rt) -> case uncap lt of ViewCap lt2 c2 -> f $ Cap (RY (B2 p1l1 p1l2) (D2 lt2 rt) s1) c2
               (DOL ot)   -> case uncap ot of ViewCap ot2 c2 -> f $ Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
               (DOR ot)   -> case uncap ot of ViewCap ot2 c2 -> f $ Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
               D0 -> error "Impossible"
    only (Cap (OOX p1 d1 s1@B8{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> f $ Triple (pushWith (S1 rem2) (plugR d1 c) $ \e -> RG (B2 p1l1 p1l2) e s1)
    only (Cap (OOX p1 d1 s1@B9{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> f $ Triple (pushWith (S1 rem2) (plugR d1 c) $ \e -> RG (B2 p1l1 p1l2) e s1)
    only (Cap (OXO p1 d1 s1) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case d1 of
                 (D2 lt rt) -> f $ Cap (RO (B2 p1l1 p1l2) (D2 (pushLeftG (S1 rem2) lt) rt) s1) c
                 (DOR ot)   -> pushOnly (S1 rem2) (cap ot c) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
           H p1l1 (NoShift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case d1 of
                 (D2 lt rt) -> f $ Cap (RO (B2 p1l1 p1l2) (D2 (pushLeftG (S1 rem2) lt) rt) s1) c
                 (DOR ot)   -> pushOnly (S1 rem2) (cap ot c) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
             H p1l2 (NoShift rem2) -> case d1 of
                 (D2 lt rt) -> f $ Cap (RO (B2 p1l1 p1l2) (D2 (pushLeftG (S1 rem2) lt) rt) s1) c
                 (DOR ot)   -> pushOnly (S1 rem2) (cap ot c) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
    only (Triple (OXR p1 d1 s1)) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case d1 of
                 (D2 lt rt) -> f $ Triple (RR (B2 p1l1 p1l2) (D2 (pushLeftG (S1 rem2) lt) rt) s1)
                 (DOR ot)   ->  f $ Triple (RR (B2 p1l1 p1l2) (DOR (pushOnly (S1 rem2) ot)) s1)
                 (DOL ot)   ->  f $ Triple (RR (B2 p1l1 p1l2) (DOR (pushOnly (S1 rem2) ot)) s1)
                 D0 -> f $ Triple (RR (B2 p1l1 p1l2) (DOR (Triple (O0 (B1 (S1 rem2))))) s1)
           H p1l1 (NoShift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case d1 of
                 (D2 lt rt) -> f $ Triple (RR (B2 p1l1 p1l2) (D2 (pushLeftG (S1 rem2) lt) rt) s1)
                 (DOR ot)   ->  f $ Triple (RR (B2 p1l1 p1l2) (DOR (pushOnly (S1 rem2) ot)) s1)
                 (DOL ot)   ->  f $ Triple (RR (B2 p1l1 p1l2) (DOR (pushOnly (S1 rem2) ot)) s1)
                 D0 -> f $ Triple (RR (B2 p1l1 p1l2) (DOR (Triple (O0 (B1 (S1 rem2))))) s1)
             H p1l2 (NoShift rem2) -> case d1 of
                 (D2 lt rt) -> f $ Triple (RR (B2 p1l1 p1l2) (D2 (pushLeftG (S1 rem2) lt) rt) s1)
                 (DOR ot)   ->  f $ Triple (RR (B2 p1l1 p1l2) (DOR (pushOnly (S1 rem2) ot)) s1)
                 (DOL ot)   ->  f $ Triple (RR (B2 p1l1 p1l2) (DOR (pushOnly (S1 rem2) ot)) s1)
                 D0 -> f $ Triple (RR (B2 p1l1 p1l2) (DOR (Triple (O0 (B1 (S1 rem2))))) s1)
    only (Cap (OYX p1 d1 s1@B7{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case plugL c d1 of
               D2 lt rt -> pushLeft (S1 rem2) lt $ \e -> case uncap e of ViewCap lt2 c2 -> f $ Cap (RY (B2 p1l1 p1l2) (D2 lt2 rt) s1) c2
               DOL ot -> pushOnly (S1 rem2) ot $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
    only (Cap (OYX p1 d1 s1@B8{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> pushWith (S1 rem2) (plugL c d1) $ \e -> f $ Triple (RG (B2 p1l1 p1l2) e s1)
    only (Cap (OYX p1 d1 s1@B9{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> pushWith (S1 rem2) (plugL c d1) $ \e -> f $ Triple (RG (B2 p1l1 p1l2) e s1)
    only (Cap (OGY p1 d1 s1) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case plugL c d1 of
               D2 lt rt -> pushLeft (S1 rem2) lt $ \e -> case uncap e of ViewCap lt2 c2 -> f $ Cap (RY (B2 p1l1 p1l2) (D2 lt2 rt) s1) c2
               DOL ot -> pushOnly (S1 rem2) ot $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
           H p1l1 (NoShift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case plugL c d1 of
               D2 lt rt -> pushLeft (S1 rem2) lt $ \e -> case uncap e of ViewCap lt2 c2 -> f $ Cap (RY (B2 p1l1 p1l2) (D2 lt2 rt) s1) c2
               DOL ot -> pushOnly (S1 rem2) ot $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
             H p1l2 (NoShift rem2) -> case plugL c d1 of
               D2 lt rt -> pushLeft (S1 rem2) lt $ \e -> case uncap e of ViewCap lt2 c2 -> f $ Cap (RY (B2 p1l1 p1l2) (D2 lt2 rt) s1) c2
               DOL ot -> pushOnly (S1 rem2) ot $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"

    onlyPS :: Buffer F F F F a5 a6 a7 a8 a9 q j' j -> Buffer F F F F b5 b6 b7 b8 b9 q i j' -> g
    onlyPS p1@B9{} s1 = case ejectB p1 of
        H (Shift rem1) p1r1 -> case ejectB rem1 of
          H (Shift rem2) p1r2 -> case ejectB rem2 of
            H (Shift rem3) p1r3 -> case popB rem3 of
              H p1l1 (Shift rem4) -> case popB rem4 of
                H p1l2 (Shift rem5) -> f $ Triple $ RG p2 (push (S1 rem5) D0) s2
                  where
                    p2 = B2 p1l1 p1l2
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
        H (NoShift rem1) p1r1 -> case ejectB rem1 of
          H (Shift rem2) p1r2 -> case ejectB rem2 of
            H (Shift rem3) p1r3 -> case popB rem3 of
              H p1l1 (Shift rem4) -> case popB rem4 of
                H p1l2 (Shift rem5) -> f $ Triple $ RG p2 (push (S1 rem5) D0) s2
                  where
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
                    p2 = B2 p1l1 p1l2
          H (NoShift rem2) p1r2 -> case ejectB rem2 of
            H (Shift rem3) p1r3 -> case popB rem3 of
              H p1l1 (Shift rem4) -> case popB rem4 of
                H p1l2 (Shift rem5) -> f $ Triple $ RG p2 (push (S1 rem5) D0) s2
                  where
                    p2 = B2 p1l1 p1l2
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
            H (NoShift rem3) p1r3 -> case popB rem3 of
              H p1l1 (Shift rem4) -> case popB rem4 of
                H p1l2 (Shift rem5) -> f $ Triple $ RG p2 (push (S1 rem5) D0) s2
                  where
                    p2 = B2 p1l1 p1l2
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
              H p1l1 (NoShift rem4) -> case popB rem4 of
                H p1l2 (Shift rem5) -> f $ Triple $ RG p2 (push (S1 rem5) D0) s2
                  where
                    p2 = B2 p1l1 p1l2
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
                H p1l2 (NoShift rem5) -> f $ Triple $ RG p2 (push (S1 rem5) D0) s2
                  where
                    p2 = B2 p1l1 p1l2
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
    onlyPS p1 s1 = case popB p1 of
      H p1l1 (Shift rem1) -> case popB rem1 of
        H p1l2 (Shift rem2) -> f $ Triple $ RG (B2 p1l1 p1l2) D0 (catenateB rem2 s1)
      H p1l1 (NoShift rem1) -> case popB rem1 of
        H p1l2 (Shift rem2) -> f $ Triple $ RG (B2 p1l1 p1l2) D0 (catenateB rem2 s1)
        H p1l2 (NoShift rem2) -> f $ Triple $ RG (B2 p1l1 p1l2) D0 (catenateB rem2 s1)

data ClosedDeque q i j where
  CD :: Deque (Closed lg) (Closed rg) q i j -> ClosedDeque q i j

data View l r a c where
  Empty :: View l r a a
  (:|) :: l b c -> r a b -> View l r a c

data View3 q a c where
  V0 :: View3 q a a
  V1 :: q a c -> View3 q a c
  V3 :: q c d -> Deque (Closed lg) (Closed rg) q b c -> q a b -> View3 q a d

popNoRepair :: forall q i j g. Deque (Closed Green) (Closed Green) q i j -> (forall lg rg. View q (Deque (Closed lg) (Closed rg) q) i j -> g) -> g
popNoRepair d f = case d of
  D0 -> f Empty
  D2 lt rt -> popLeftNoRepair lt $ \e -> case e of
    Left (H a b) -> f . (a :|) . DOL $ case rt of
      Triple (R0 p1 s1) -> Triple $ O0 (catenateB b (catenateB p1 s1))
      Triple (RG p1 d1 s1) -> Triple $ OGG (catenateB b p1) d1 s1
      Cap (RO p1 d1 s1) cap1 -> Cap (OXO (catenateB b p1) d1 s1) cap1
      Cap (RY p1 d1 s1) cap1 -> Cap (OGY (catenateB b p1) d1 s1) cap1
    Right (H a lt') -> f $ a :| D2 lt' rt
  DOL ot -> popOnlyNoRepair ot f
  DOR ot -> popOnlyNoRepair ot f

popLeftNoRepair :: Cap LeftTriple (Closed Green) q j k
                -> ((forall lg. Either (HPair q (Buffer F F F F F T F F F q) j k)
                                       (HPair q (Cap LeftTriple (Closed lg) q) j k) -> g) -> g)
popLeftNoRepair c f = case c of
  Triple (LG p1 d1 s1) -> case popB p1 of
    H p1l1 (Shift rem1@B7{}) -> case d1 of
      D2 lt2 rt2 -> case uncap lt2 of ViewCap lt3 cap3 -> f . Right $ p1l1 `H` Cap (LY rem1 (D2 lt3 rt2) s1) cap3
      DOL ot -> case uncap ot of ViewCap ot2 cap2 -> f . Right $ p1l1 `H` Cap (LY rem1 (DOL ot2) s1) cap2
      DOR ot -> case uncap ot of ViewCap ot2 cap2 -> f . Right $ p1l1 `H` Cap (LY rem1 (DOL ot2) s1) cap2
      D0 -> f . Right $ p1l1 `H` Triple (L0 rem1 s1)
    H p1l1 (Shift rem1@B8{}) -> f . Right $ p1l1 `H` Triple (LG rem1 d1 s1)
    H p1l1 (NoShift rem1) -> f . Right $ p1l1 `H` Triple (LG rem1 d1 s1)
  Cap (LY p1 d1 s1) cap1 -> case popB p1 of
    H p1l1 (Shift rem1) -> case d1 of
      D2 lt2 rt2 -> case uncap rt2 of ViewCap rt3 cap3 -> f . Right $ p1l1 `H` Cap (LO rem1 (D2 (cap lt2 cap1) rt3) s1) cap3
      DOL ot -> f . Right $ p1l1 `H` Cap (LO rem1 (DOR ot) s1) cap1
  Cap (LO p1 d1 s1) cap1 -> case popB p1 of
    H p1l1 (Shift rem1) -> case d1 of
      D2 lt2 rt2 -> f . Right $ p1l1 `H` Triple (LR rem1 (D2 lt2 (cap rt2 cap1)) s1)
      DOR ot -> f . Right $ p1l1 `H` Triple (LR rem1 (DOR (cap ot cap1)) s1)
  Triple (L0 p1 s1) -> case popB p1 of
    H p1l1 (Shift rem1@B4{}) -> f . Left $ p1l1 `H` catenateB rem1 s1
      --                           \rt -> case rt of
      -- Triple (R0 lt2 rt2) -> p1l1 `H` Triple (O0 (catenateB rem1 (catenateB s1 (catenateB lt2 rt2))))
      -- Triple (RG lt2 d2 rt2) -> p1l1 `H` Triple (OGG (catenateB rem1 (catenateB s1 lt2)) d2 rt2)
      -- Cap (RY lt2 d2 rt2) cap2 -> p1l1 `H` Cap (OGY (catenateB rem1 (catenateB s1 lt2)) d2 rt2) cap2
      -- Cap (RO lt2 d2 rt2) cap2 -> p1l1 `H` Cap (OXO (catenateB rem1 (catenateB s1 lt2)) d2 rt2) cap2
      -- Triple (RR lt2 d2 rt2) -> p1l1 `H` Triple (OXR (catenateB rem1 (catenateB s1 lt2)) d2 rt2)
    H p1l1 (Shift rem1@B5{}) -> f . Right $ p1l1 `H` Triple (L0 rem1 s1)
    H p1l1 (Shift rem1@B6{}) -> f . Right $ p1l1 `H` Triple (L0 rem1 s1)
    H p1l1 (Shift rem1@B7{}) -> f . Right $ p1l1 `H` Triple (L0 rem1 s1)
    H p1l1 (Shift rem1@B8{}) -> f . Right $ p1l1 `H` Triple (L0 rem1 s1)
    H p1l1 (NoShift rem1) -> f . Right $ p1l1 `H` Triple (L0 rem1 s1)

ejectRightNoRepair :: Cap RightTriple (Closed Green) q i j
                -> ((forall rg. Either (HPair (Buffer F F F F F T F F F q) q i j)
                                       (HPair (Cap RightTriple (Closed rg) q) q i j) -> g) -> g)
ejectRightNoRepair c f = case c of
  Triple (RG p1 d1 s1) -> case ejectB s1 of
    H (Shift rem1@B7{}) s1r1 -> case d1 of
      D2 lt2 rt2 -> case uncap lt2 of ViewCap lt3 cap3 -> f . Right $ Cap (RY p1 (D2 lt3 rt2) rem1) cap3 `H` s1r1
      DOL ot -> case uncap ot of ViewCap ot2 cap2 -> f . Right $ Cap (RY p1 (DOL ot2) rem1) cap2 `H` s1r1
      DOR ot -> case uncap ot of ViewCap ot2 cap2 -> f . Right $ Cap (RY p1 (DOL ot2) rem1) cap2 `H` s1r1
      D0 -> f . Right $  Triple (R0 p1 rem1) `H` s1r1
    H (Shift rem1@B8{}) s1r1 -> f . Right $ Triple (RG p1 d1 rem1) `H` s1r1
    H (NoShift rem1) s1r1 -> f . Right $ Triple (RG p1 d1 rem1) `H` s1r1
  Cap (RY p1 d1 s1) cap1 -> case ejectB s1 of
    H (Shift rem1) s1r1 -> case d1 of
      D2 lt2 rt2 -> case uncap rt2 of ViewCap rt3 cap3 -> f . Right $ Cap (RO p1 (D2 (cap lt2 cap1) rt3) rem1) cap3 `H` s1r1
      DOL ot -> f . Right $ Cap (RO p1 (DOR ot) rem1) cap1 `H` s1r1
  Cap (RO p1 d1 s1) cap1 -> case ejectB s1 of
    H (Shift rem1) s1r1 -> case d1 of
      D2 lt2 rt2 -> f . Right $ Triple (RR p1 (D2 lt2 (cap rt2 cap1)) rem1) `H` s1r1
      DOR ot -> f . Right $ Triple (RR p1 (DOR (cap ot cap1)) rem1) `H` s1r1
  Triple (R0 p1 s1) -> case ejectB s1 of
    H (Shift rem1@B4{}) s1r1 -> f . Left $ catenateB p1 rem1 `H` s1r1
    H (Shift rem1@B5{}) s1r1 -> f . Right $ Triple (R0 p1 rem1) `H` s1r1
    H (Shift rem1@B6{}) s1r1 -> f . Right $ Triple (R0 p1 rem1) `H` s1r1
    H (Shift rem1@B7{}) s1r1 -> f . Right $ Triple (R0 p1 rem1) `H` s1r1
    H (Shift rem1@B8{}) s1r1 -> f . Right $ Triple (R0 p1 rem1) `H` s1r1
    H (NoShift rem1)    s1r1 -> f . Right $ Triple (R0 p1 rem1) `H` s1r1

popOnlyNoRepair :: Cap OnlyTriple (Closed Green) q i j -> (forall lg rg. View q (Deque (Closed lg) (Closed rg) q) i j -> g) -> g
popOnlyNoRepair (Triple (O0 p1)) f = case popB p1 of
      H p1l1 NoB -> f $ p1l1 :| D0
      H p1l1 (Shift rem1) -> f $ p1l1 :| (DOL (Triple (O0 rem1)))
      H p1l1 (NoShift rem1) -> f $ p1l1 :| (DOL (Triple (O0 rem1)))
popOnlyNoRepair (Triple (OGG p1 d1 s1)) f = case popB p1 of
      H p1l1 (Shift rem1@B7{}) -> case d1 of
        D2 lt2 rt2 -> case uncap lt2 of ViewCap lt3 cap3 -> f $ p1l1 :| (DOL (Cap (OYX rem1 (D2 lt3 rt2) s1) cap3))
        DOL ot -> case uncap ot of ViewCap ot3 cap3 -> f $ p1l1 :| (DOL (Cap (OYX rem1 (DOL ot3) s1) cap3))
        DOR ot -> case uncap ot of ViewCap ot3 cap3 -> f $ p1l1 :| (DOL (Cap (OYX rem1 (DOL ot3) s1) cap3))
        D0 -> f $ p1l1 :| (DOL (Triple (O0 (catenateB rem1 s1))))
      H p1l1 (Shift rem1@B8{}) -> f $ p1l1 :| (DOL (Triple (OGG rem1 d1 s1)))
      H p1l1 (NoShift rem1) -> f $ p1l1 :| (DOL (Triple (OGG rem1 d1 s1)))
popOnlyNoRepair (Cap (OOX p1 d1 s1) cap1) f = case popB p1 of
      H p1l1 (Shift rem1) -> f $ p1l1 :| (DOL (Triple (ORX rem1 (plugR d1 cap1) s1)))
popOnlyNoRepair (Cap (OXO p1 d1 s1) cap1) f = case popB p1 of
      H p1l1 (Shift rem1@B6{}) -> f $ p1l1 :| (DOL (Cap (OOX rem1 d1 s1) cap1))
      H p1l1 (Shift rem1@B7{}) -> f $ p1l1 :| (DOL (Cap (OXO rem1 d1 s1) cap1))
      H p1l1 (Shift rem1@B8{}) -> f $ p1l1 :| (DOL (Cap (OXO rem1 d1 s1) cap1))
      H p1l1 (NoShift rem1)    -> f $ p1l1 :| (DOL (Cap (OXO rem1 d1 s1) cap1))
popOnlyNoRepair (Cap (OYX p1 d1 s1) cap1) f = case popB p1 of
      H p1l1 (Shift rem1) -> case d1 of
        D2 lt2 rt2 -> case uncap rt2 of ViewCap rt3 cap3 -> f $ p1l1 :| (DOL (Cap (OOX rem1 (D2 (cap lt2 cap1) rt3) s1) cap3))
        DOL ot -> f $ p1l1 :| (DOL (Cap (OOX rem1 (DOR ot) s1) cap1))
popOnlyNoRepair (Cap (OGY p1 d1 s1) cap1) f = case popB p1 of
      H p1l1 (Shift rem1@B7{}) -> f $ p1l1 :| (DOL (Cap (OYX rem1 d1 s1) cap1))
      H p1l1 (Shift rem1@B8{}) -> f $ p1l1 :| (DOL (Cap (OGY rem1 d1 s1) cap1))
      H p1l1 (NoShift rem1)    -> f $ p1l1 :| (DOL (Cap (OGY rem1 d1 s1) cap1))

popEjectOnlyNoRepair :: Cap OnlyTriple (Closed Green) q i j -> View3 q i j
popEjectOnlyNoRepair (Triple (O0 p1)) = case popB p1 of
      H p1l1 NoB -> V1 p1l1
      H p1l1 (Shift rem1) -> case ejectB rem1 of
        H (Shift rem2) p1r1 -> V3 p1l1 (DOL (Triple (O0 rem2))) p1r1
      H p1l1 (NoShift rem1) -> case ejectB rem1 of
        H (Shift rem2) p1r1 -> V3 p1l1 (DOL (Triple (O0 rem2))) p1r1
        H (NoShift rem2) p1r1 -> V3 p1l1 (DOL (Triple (O0 rem2))) p1r1
popEjectOnlyNoRepair (Triple (OGG p1 d1 s1)) = case popB p1 of
      H p1l1 (Shift rem1@B7{}) -> case ejectB s1 of
        H (Shift rem2) s1r1 -> case d1 of
          D2 lt2 rt2 -> case uncap lt2 of ViewCap lt3 cap3 -> V3 p1l1 (DOL (Cap (OYX rem1 (D2 lt3 rt2) rem2) cap3)) s1r1
          DOL ot -> case uncap ot of ViewCap ot3 cap3 -> V3 p1l1 (DOL (Cap (OYX rem1 (DOL ot3) rem2) cap3)) s1r1
          DOR ot -> case uncap ot of ViewCap ot3 cap3 -> V3 p1l1 (DOL (Cap (OYX rem1 (DOL ot3) rem2) cap3)) s1r1
          D0 -> V3 p1l1 (DOL (Triple (O0 (catenateB rem1 rem2)))) s1r1
        H (NoShift rem2) s1r1 -> case d1 of
          D2 lt2 rt2 -> case uncap lt2 of ViewCap lt3 cap3 -> V3 p1l1 (DOL (Cap (OYX rem1 (D2 lt3 rt2) rem2) cap3)) s1r1
          DOL ot -> case uncap ot of ViewCap ot3 cap3 -> V3 p1l1 (DOL (Cap (OYX rem1 (DOL ot3) rem2) cap3)) s1r1
          DOR ot -> case uncap ot of ViewCap ot3 cap3 -> V3 p1l1 (DOL (Cap (OYX rem1 (DOL ot3) rem2) cap3)) s1r1
          D0 -> V3 p1l1 (DOL (Triple (O0 (catenateB rem1 rem2)))) s1r1
      H p1l1 (Shift rem1@B8{}) -> case ejectB s1 of
        H (Shift rem2@B7{}) s1r1 -> case d1 of
          D2 lt2 rt2 -> case uncap lt2 of ViewCap lt3 cap3 -> V3 p1l1 (DOL (Cap (OGY rem1 (D2 lt3 rt2) rem2) cap3)) s1r1
          DOL ot -> case uncap ot of ViewCap ot3 cap3 -> V3 p1l1 (DOL (Cap (OGY rem1 (DOL ot3) rem2) cap3)) s1r1
          DOR ot -> case uncap ot of ViewCap ot3 cap3 -> V3 p1l1 (DOL (Cap (OGY rem1 (DOL ot3) rem2) cap3)) s1r1
          D0 -> V3 p1l1 (DOL (Triple (O0 (catenateB rem1 rem2)))) s1r1
        H (Shift rem2@B8{}) s1r1 -> V3 p1l1 (DOL (Triple (OGG rem1 d1 rem2))) s1r1
        H (NoShift rem2) s1r1 -> V3 p1l1 (DOL (Triple (OGG rem1 d1 rem2))) s1r1
      H p1l1 (NoShift rem1) -> case ejectB s1 of
        H (Shift rem2@B7{}) s1r1 -> case d1 of
          D2 lt2 rt2 -> case uncap lt2 of ViewCap lt3 cap3 -> V3 p1l1 (DOL (Cap (OGY rem1 (D2 lt3 rt2) rem2) cap3)) s1r1
          DOL ot -> case uncap ot of ViewCap ot3 cap3 -> V3 p1l1 (DOL (Cap (OGY rem1 (DOL ot3) rem2) cap3)) s1r1
          DOR ot -> case uncap ot of ViewCap ot3 cap3 -> V3 p1l1 (DOL (Cap (OGY rem1 (DOL ot3) rem2) cap3)) s1r1
          D0 -> V3 p1l1 (DOL (Triple (O0 (catenateB rem1 rem2)))) s1r1
        H (Shift rem2@B8{}) s1r1 -> V3 p1l1 (DOL (Triple (OGG rem1 d1 rem2))) s1r1
        H (NoShift rem2) s1r1 -> V3 p1l1 (DOL (Triple (OGG rem1 d1 rem2))) s1r1
popEjectOnlyNoRepair (Cap (OOX p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> case ejectB s1 of
        H (Shift rem2) s1r1 -> V3 p1l1 (DOL (Triple (ORX rem1 (plugR d1 cap1) rem2))) s1r1
        H (NoShift rem2) s1r1 -> V3 p1l1 (DOL (Triple (ORX rem1 (plugR d1 cap1) rem2))) s1r1
popEjectOnlyNoRepair (Cap (OXO p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> case ejectB s1 of
        H (Shift rem2) s1r1 -> V3 p1l1 (DOL (Triple (OXR rem1 (plugR d1 cap1) rem2))) s1r1
      H p1l1 (NoShift rem1) -> case ejectB s1 of
        H (Shift rem2) s1r1 -> V3 p1l1 (DOL (Triple (OXR rem1 (plugR d1 cap1) rem2))) s1r1
popEjectOnlyNoRepair (Cap (OYX p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> case ejectB s1 of
        H (Shift rem2) s1r1 -> case d1 of
          D2 lt2 rt2 -> case uncap rt2 of ViewCap rt3 cap3 -> V3 p1l1 (DOL (Cap (OOX rem1 (D2 (cap lt2 cap1) rt3) rem2) cap3)) s1r1
          DOL ot -> V3 p1l1 (DOL (Cap (OOX rem1 (DOR ot) rem2) cap1)) s1r1
        H (NoShift rem2) s1r1 -> case d1 of
          D2 lt2 rt2 -> case uncap rt2 of ViewCap rt3 cap3 -> V3 p1l1 (DOL (Cap (OOX rem1 (D2 (cap lt2 cap1) rt3) rem2) cap3)) s1r1
          DOL ot -> V3 p1l1 (DOL (Cap (OOX rem1 (DOR ot) rem2) cap1)) s1r1
popEjectOnlyNoRepair (Cap (OGY p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> case ejectB s1 of
        H (Shift rem2) s1r1 -> case d1 of
          D2 lt2 rt2 -> case uncap rt2 of ViewCap rt3 cap3 -> V3 p1l1 (DOL (Cap (OXO rem1 (D2 (cap lt2 cap1) rt3) rem2) cap3)) s1r1
          DOL ot -> V3 p1l1 (DOL (Cap (OXO rem1 (DOR ot) rem2) cap1)) s1r1
      H p1l1 (NoShift rem1) -> case ejectB s1 of
        H (Shift rem2) s1r1 -> case d1 of
          D2 lt2 rt2 -> case uncap rt2 of ViewCap rt3 cap3 -> V3 p1l1 (DOL (Cap (OXO rem1 (D2 (cap lt2 cap1) rt3) rem2) cap3)) s1r1
          DOL ot -> V3 p1l1 (DOL (Cap (OXO rem1 (DOR ot) rem2) cap1)) s1r1

ejectOnlyNoRepair :: Cap OnlyTriple (Closed Green) q i j -> (forall lg rg. View (Deque (Closed lg) (Closed rg) q) q i j -> g) -> g
ejectOnlyNoRepair c f = case popEjectOnlyNoRepair c of
  V0 -> f Empty
  V1 a -> f (D0 :| a)
  V3 a b c -> pushWith a b $ \d -> f (d :| c)

ejectNoRepair :: forall q i j g. Deque (Closed Green) (Closed Green) q i j -> (forall lg rg. View (Deque (Closed lg) (Closed rg) q) q i j -> g) -> g
ejectNoRepair d f = case d of
  D0 -> f Empty
  D2 lt rt -> ejectRightNoRepair rt $ \e -> case e of
    Left (b `H` r) -> f . ( :| r) . DOL $ case lt of
      Triple (L0 p1 s1) -> Triple (O0 (catenateB (catenateB p1 s1) b))
      Triple (LG p1 d1 s1) -> Triple (OGG p1 d1 (catenateB s1 b))
      Cap (LO p1 d1 s1) cap1 -> Cap (OOX p1 d1 (catenateB s1 b)) cap1
      Cap (LY p1 d1 s1) cap1 -> Cap (OYX p1 d1 (catenateB s1 b)) cap1
    Right (rt' `H` r) -> f $ D2 lt rt' :| r
  DOL ot -> ejectOnlyNoRepair ot f
  DOR ot -> ejectOnlyNoRepair ot f

popEjectNoRepair :: forall q i j. Deque (Closed Green) (Closed Green) q i j -> View3 q i j
popEjectNoRepair D0 = V0
popEjectNoRepair (DOL ot) = popEjectOnlyNoRepair ot
popEjectNoRepair (DOR ot) = popEjectOnlyNoRepair ot
popEjectNoRepair (D2 lt rt) = popLeftNoRepair lt $ \le -> ejectRightNoRepair rt $ \re -> case (le, re) of
  (Right (H l1 lt'), Right (H rt' r1)) -> V3 l1 (D2 lt' rt') r1
  (Right (H l1 lt'), Left (H rb r1)) -> case lt' of
    Triple (LG p2 d2 s2) -> V3 l1 (DOL (Triple (OGG p2 d2 (catenateB s2 rb)))) r1
    Triple (LR p2 d2 s2) -> V3 l1 (DOL (Triple (ORX p2 d2 (catenateB s2 rb)))) r1
    Triple (L0 p2 s2) -> V3 l1 (DOL (Triple (O0 (catenateB (catenateB p2 s2) rb)))) r1
    Cap (LO p2 d2 s2) cap1 -> V3 l1 (DOL (Cap (OOX p2 d2 (catenateB s2 rb)) cap1)) r1
    Cap (LY p2 d2 s2) cap1 -> V3 l1 (DOL (Cap (OYX p2 d2 (catenateB s2 rb)) cap1)) r1
  (Left (H l1 lb), Right (H rt' r1)) -> case rt' of
    Triple (RG p2 d2 s2) -> V3 l1 (DOL (Triple (OGG (catenateB lb p2) d2 s2))) r1
    Triple (RR p2 d2 s2) -> V3 l1 (DOL (Triple (OXR (catenateB lb p2) d2 s2))) r1
    Triple (R0 p2 s2) -> V3 l1 (DOL (Triple (O0 (catenateB lb (catenateB p2 s2))))) r1
    Cap (RO p2 d2 s2) cap1 -> V3 l1 (DOL (Cap (OXO (catenateB lb p2) d2 s2) cap1)) r1
    Cap (RY p2 d2 s2) cap1 -> V3 l1 (DOL (Cap (OGY (catenateB lb p2) d2 s2) cap1)) r1
  (Left (H l1 lb), Left (H rb r1)) -> V3 l1 (DOL (Triple (O0 (catenateB lb rb)))) r1

popThenPush :: forall lg lr q i k foo m. (Monad m) => Deque (Closed lg) (Closed lr) q i k -> (forall j. q j k -> m (HPair foo q j k)) -> m (View foo (Deque (Closed lg) (Closed lr) q) i k)
popThenPush d f = case d of
  D0 -> return Empty
  D2 (Triple (LG p1 d1 s1)) rt -> case popB p1 of
    H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo :| D2 (Triple (LG (pushB q rem1) d1 s1)) rt
    H p1l1 (NoShift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo :| D2 (Triple (LG (pushB q rem1) d1 s1)) rt
  D2 (Triple (L0 p1 s1)) rt -> case popB p1 of
    H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo :| D2 (Triple (L0 (pushB q rem1) s1)) rt
    H p1l1 (NoShift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo :| D2 (Triple (L0 (pushB q rem1) s1)) rt
  D2 (Triple (LR p1 d1 s1)) rt -> case popB p1 of
    H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo :| D2 (Triple (LR (pushB q rem1) d1 s1)) rt
  D2 (Cap (LY p1 d1 s1) cap1) rt -> case popB p1 of
    H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo :| D2 (Cap (LY (pushB q rem1) d1 s1) cap1) rt
  D2 (Cap (LO p1 d1 s1) cap1) rt -> case popB p1 of
    H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo :| D2 (Cap (LO (pushB q rem1) d1 s1) cap1) rt
  DOL ot -> only ot >>= \bar -> case bar of H foo c -> return $ foo :| DOL c
  DOR ot -> only ot >>= \bar -> case bar of H foo c -> return $ foo :| DOR c
  where
    only :: Cap OnlyTriple (Closed cl) q i' k -> m (HPair foo (Cap OnlyTriple (Closed cl) q) i' k)
    only (Triple (O0 p1)) = case popB p1 of
      H p1l1 NoB -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo `H` (Triple (O0 (B1 q)))
      H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo `H` (Triple (O0 (pushB q rem1)))
      H p1l1 (NoShift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo `H` (Triple (O0 (pushB q rem1)))
    only (Triple (OGG p1 d1 s1)) = case popB p1 of
      H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo `H` (Triple (OGG (pushB q rem1) d1 s1))
      H p1l1 (NoShift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo `H` (Triple (OGG (pushB q rem1) d1 s1))
    only (Triple (ORX p1 d1 s1)) = case popB p1 of
      H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo `H` (Triple (ORX (pushB q rem1) d1 s1))
    only (Triple (OXR p1 d1 s1)) = case popB p1 of
      H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo `H` (Triple (OXR (pushB q rem1) d1 s1))
      H p1l1 (NoShift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo `H` (Triple (OXR (pushB q rem1) d1 s1))
    only (Cap (OXO p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of H foo q -> return $ foo `H` (Cap (OXO (pushB q rem1) d1 s1) cap1)
      H p1l1 (NoShift rem1) -> f p1l1 >>= \bar -> case bar of H foo q -> return $ foo `H` (Cap (OXO (pushB q rem1) d1 s1) cap1)
    only (Cap (OOX p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of H foo q -> return $ foo `H` (Cap (OOX (pushB q rem1) d1 s1) cap1)
    only (Cap (OYX p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of H foo q -> return $ foo `H` (Cap (OYX (pushB q rem1) d1 s1) cap1)
    only (Cap (OGY p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of H foo q -> return $ foo `H` (Cap (OGY (pushB q rem1) d1 s1) cap1)
      H p1l1 (NoShift rem1) -> f p1l1 >>= \bar -> case bar of H foo q -> return $ foo `H` (Cap (OGY (pushB q rem1) d1 s1) cap1)

data SomeBuffer3 q j k where
  SB3 :: Buffer F F k3 k4 k5 k6 k7 k8 k9 q j k -> SomeBuffer3 q j k

repairLeftTriple :: LeftTriple (Closed c) q i j -> LeftTriple (Closed Green) q i j
repairLeftTriple l = case l of
  (LR p1 d1 s1) -> popNoRepair d1 $ \v -> case v of
    (S3 p2 d2 s2) :| d1' -> pushWith (S1 s2) d1' $ \d1'' ->
      catenate' d2 d1'' $ \d3 ->
      LG (catenateB p1 p2) d3 s1
    (S1 p2) :| d1' -> LG (catenateB p1 p2) d1' s1
    Empty -> L0 p1 s1
  L0{} -> l
  LG{} -> l

repairCap :: Repairable r => Cap r (Closed c) q i j -> Cap r (Closed Green) q i j
repairCap c = case uncap c of
  ViewCap t c' -> cap t (repair c')

repairRightTriple :: RightTriple (Closed c) q i j -> RightTriple (Closed Green) q i j
repairRightTriple r = case r of
  (RR p1 d1 s1) -> ejectNoRepair d1 $ \v -> case v of
    d1' :| (S3 p2 d2 s2) -> injectWith d1' (S1 p2) $ \d1'' ->
      catenate' d1'' d2 $ \d3 ->
      RG p1 d3 (catenateB s2 s1)
    d1' :| (S1 p2) -> RG p1 d1' (catenateB p2 s1)
    Empty -> R0 p1 s1
  R0{} -> r
  RG{} -> r

repairOnlyTriple :: OnlyTriple (Closed c) q i j -> OnlyTriple (Closed Green) q i j
repairOnlyTriple o = case o of
  (ORX p1 d1 s1@B8{}) -> popNoRepair d1 $ \v -> case v of
    (S3 p2 d2 s2) :| d1' -> pushWith (S1 s2) d1' $ \d1'' ->
      catenate' d2 d1'' $ \d3 ->
      OGG (catenateB p1 p2) d3 s1
    (S1 p2) :| d1' -> OGG (catenateB p1 p2) d1' s1
    Empty -> O0 (catenateB p1 s1)
  (ORX p1 d1 s1@B9{}) -> popNoRepair d1 $ \v -> case v of
    (S3 p2 d2 s2) :| d1' -> pushWith (S1 s2) d1' $ \d1'' ->
      catenate' d2 d1'' $ \d3 ->
      OGG (catenateB p1 p2) d3 s1
    (S1 p2) :| d1' -> OGG (catenateB p1 p2) d1' s1
    Empty -> O0 (catenateB p1 s1)
  (OXR p1@B8{} d1 s1) -> ejectNoRepair d1 $ \v -> case v of
    d1' :| (S3 p2 d2 s2) -> injectWith d1' (S1 p2) $ \d1'' ->
      catenate' d1'' d2 $ \d3 ->
      OGG p1 d3 (catenateB s2 s1)
    d1' :| (S1 p2) -> OGG p1 d1' (catenateB p2 s1)
    Empty -> O0 (catenateB p1 s1)
  (OXR p1@B9{} d1 s1) -> ejectNoRepair d1 $ \v -> case v of
    d1' :| (S3 p2 d2 s2) -> injectWith d1' (S1 p2) $ \d1'' ->
      catenate' d1'' d2 $ \d3 ->
      OGG p1 d3 (catenateB s2 s1)
    d1' :| (S1 p2) -> OGG p1 d1' (catenateB p2 s1)
    Empty -> O0 (catenateB p1 s1)
  ORX p1 d1 s1 -> go p1 d1 s1
  OXR p1 d1 s1 -> go p1 d1 s1
  OGG{} -> o
  O0{} -> o
  where
    go :: Buffer F F F F a5 a6 a7 a8 a9 q k l -> Deque (Closed Green) (Closed Green) (StoredTriple q) j k -> Buffer F F F F b5 b6 b7 b8 b9 q i j -> OnlyTriple (Closed Green) q i l
    go p1 d1 s1 = case popEjectNoRepair d1 of
      V0 -> O0 (catenateB p1 s1)
      V1 (S1 p2) -> O0 (catenateB (catenateB p1 p2) s1)
      V1 (S3 p2 d2 s2) -> OGG (catenateB p1 p2) d2 (catenateB s2 s1)
      V3 (S1 p2) d1'' (S1 p3) -> OGG (catenateB p1 p2) d1'' (catenateB p3 s1)
      V3 (S3 p2 d2 s2) d1'' (S1 p3) -> pushWith (S1 s2) d1'' $ \d1''' -> catenate' d2 d1''' $ \d4 -> OGG (catenateB p1 p2) d4 (catenateB p3 s1)
      V3 (S1 p2) d1'' (S3 p3 d3 s3) -> injectWith d1'' (S1 p3) $ \d1''' -> catenate' d1''' d3 $ \d4 -> OGG (catenateB p1 p2) d4 (catenateB s3 s1)
      V3 (S3 p2 d2 s2) d1' (S3 p3 d3 s3) -> pushWith (S1 s2) d1' $ \d1'' -> injectWith d1'' (S1 p3) $ \d1''' -> catenate' d2 d1''' $ \d4 -> catenate' d4 d3 $ \d5 -> OGG (catenateB p1 p2) d5 (catenateB s3 s1)

instance Repairable LeftTriple where repair = repairLeftTriple

instance Repairable OnlyTriple where repair = repairOnlyTriple

instance Repairable RightTriple where repair = repairRightTriple

pop :: Deque (Closed Green) (Closed Green) q i j -> View q (Deque (Closed Green) (Closed Green) q) i j
pop d = popNoRepair d $ \v -> case v of
  Empty -> Empty
  a :| D2 lt rt -> a :| D2 (repairCap lt) (repairCap rt) -- Right triple shouldn't need repair here.
  a :| DOL ot -> a :| DOL (repairCap ot)
  a :| DOR ot -> a :| DOR (repairCap ot)
  a :| D0 -> a :| D0

data Foo a b where
  F :: !Int -> Foo () ()

instance NFData (Foo a b) where
  rnf !_ = ()

deriving instance Show (Foo a b)

mkDeq :: Int -> Int -> Deque (Closed Green) (Closed Green) Foo () ()
mkDeq m n = foldr (\a d -> catenate d $ iterate (push (F a)) empty !! m) empty [1..n]

sumDeq :: Deque (Closed Green) (Closed Green) Foo () () -> Int
sumDeq = sum . unfoldr go
  where
    go :: Deque (Closed Green) (Closed Green) Foo () () -> Maybe (Int, Deque (Closed Green) (Closed Green) Foo () ())
    go d = case pop d of
      F a :| d' -> Just (a, d')
      Empty -> Nothing

mkSeq :: Int -> Int -> Seq.Seq (Foo () ())
mkSeq m n = foldr (\a d -> (d Seq.><) $ iterate ((Seq.<|) (F a)) Seq.empty !! m) Seq.empty [1..n]

sumSeq :: Seq.Seq (Foo () ()) -> Int
sumSeq = sum . unfoldr go
  where
    go :: Seq.Seq (Foo () ()) -> Maybe (Int, Seq.Seq (Foo () ()))
    go s = case Seq.viewl s of
      F a Seq.:< d' -> Just (a, d')
      Seq.EmptyL -> Nothing
