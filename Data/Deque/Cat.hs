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

shiftless :: ViewB q i j -> Buffer q i j
shiftless (Shift b) = b
shiftless (NoShift b) = b
shiftless NoB = error "Impossible"

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

instance NFData (OnlyTriple q i j) where
  rnf !_ = ()

deriving instance Show (OnlyTriple q i j)

data LeftTriple q i j where
  L0 :: !(Buffer q k l) -> !(Buffer q j k) -> LeftTriple q j l
  LR :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> LeftTriple q j m
  LO :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> LeftTriple q j m
  LY :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> LeftTriple q j m
  LG :: !(Buffer q l m) -> !(Deque (StoredTriple q) k l) -> !(Buffer q j k) -> LeftTriple q j m

instance NFData (LeftTriple q i j) where
  rnf !_ = ()

deriving instance Show (LeftTriple q i j)

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

data RightTriple q i j where
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

pushOnly :: q j k -> Cap OnlyTriple q i j -> Cap OnlyTriple q i k
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
catenateB (B1 a) br = pushB a br
catenateB (B2 a b) br = pushB a $ pushB b br
catenateB (B3 a b c) br = pushB a $ pushB b $ pushB c br
catenateB (B4 a b c d) br = pushB a $ pushB b $ pushB c $ pushB d br
catenateB (B5 a b c d e) br =  pushB a $ pushB b $ pushB c $ pushB d $ pushB e br
catenateB (B6 a b c d e f) br = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f br
catenateB (B7 a b c d e f g) br = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g br
catenateB (B8 a b c d e f g h) br = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h br
catenateB bl@B9{} (B1 a) = injectB bl a
catenateB bl@B9{} (B2 a b) = injectB (injectB bl a) b
catenateB bl@B9{} (B3 a b c) = injectB (injectB (injectB bl a) b) c
catenateB bl@B9{} (B4 a b c d) = injectB (injectB (injectB (injectB bl a) b) c) d
catenateB bl@B9{} (B5 a b c d e) = injectB (injectB (injectB (injectB (injectB bl a) b) c) d) e
catenateB bl@B9{} (B6 a b c d e f) = injectB (injectB (injectB (injectB (injectB (injectB bl a) b) c) d) e) f
catenateB bl@B9{} (B7 a b c d e f g) = injectB (injectB (injectB (injectB (injectB (injectB (injectB bl a) b) c) d) e) f) g
catenateB bl@B9{} (B8 a b c d e f g h) = injectB (injectB (injectB (injectB (injectB (injectB (injectB (injectB bl a) b) c) d) e) f) g) h
catenateB B9{} B9{} = error "Bad"

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
catenate (DOL (Triple (O0 bl))) (DOL ot) = DOL (cat0O bl ot)
catenate (DOL (Triple (O0 bl))) (DOR ot) = DOL (cat0O bl ot)
catenate (DOR (Triple (O0 bl))) (D2 lt rt) = D2 (onlyL bl lt) rt
catenate (DOR (Triple (O0 bl))) (DOL ot) = DOL (cat0O bl ot)
catenate (DOR (Triple (O0 bl))) (DOR ot) = DOL (cat0O bl ot)
-- Case 3
catenate (D2 lt rt) (DOL (Triple (O0 br))) = D2 lt (onlyR rt br)
catenate (DOL ot)   (DOL (Triple (O0 br))) = DOL (catO0 ot br)
catenate (DOR ot)   (DOL (Triple (O0 br))) = DOL (catO0 ot br)
catenate (D2 lt rt) (DOR (Triple (O0 br))) = D2 lt (onlyR rt br)
catenate (DOL ot)   (DOR (Triple (O0 br))) = DOL (catO0 ot br)
catenate (DOR ot)   (DOR (Triple (O0 br))) = DOL (catO0 ot br)
-- Case 1
catenate d e = D2 (fixLeft d) (fixRight e)

catenate' :: Deque q j k -> Deque q i j -> Deque q i k
-- Trivial
catenate' D0 a = a
catenate' a D0 = a
-- Case 4:
catenate' (DOL (Triple (O0 bl@B8{}))) (DOL (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOL (Triple (O0 bl@B9{}))) (DOL (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOL (Triple (O0 bl@B8{}))) (DOL (Triple (O0 br@B9{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOL (Triple (O0 bl@B9{}))) (DOL (Triple (O0 br@B9{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOL (Triple (O0 bl)))      (DOL (Triple (O0 br)))      = DOL (Triple (O0 (catenateB bl br)))
catenate' (DOL (Triple (O0 bl@B8{}))) (DOR (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOL (Triple (O0 bl@B8{}))) (DOR (Triple (O0 br@B9{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOL (Triple (O0 bl@B9{}))) (DOR (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOL (Triple (O0 bl@B9{}))) (DOR (Triple (O0 br@B9{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOL (Triple (O0 bl)))      (DOR (Triple (O0 br)))      = DOL (Triple (O0 (catenateB bl br)))
catenate' (DOR (Triple (O0 bl@B8{}))) (DOL (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOR (Triple (O0 bl@B8{}))) (DOL (Triple (O0 br@B9{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOR (Triple (O0 bl@B9{}))) (DOL (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOR (Triple (O0 bl@B9{}))) (DOL (Triple (O0 br@B9{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOR (Triple (O0 bl)))      (DOL (Triple (O0 br)))      = DOL (Triple (O0 (catenateB bl br)))
catenate' (DOR (Triple (O0 bl@B8{}))) (DOR (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOR (Triple (O0 bl@B8{}))) (DOR (Triple (O0 br@B9{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOR (Triple (O0 bl@B9{}))) (DOR (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOR (Triple (O0 bl@B9{}))) (DOR (Triple (O0 br@B9{}))) = DOL (Triple (OGG bl D0 br))
catenate' (DOR (Triple (O0 bl)))      (DOR (Triple (O0 br)))      = DOL (Triple (O0 (catenateB bl br)))
-- -- Case 2:
catenate' (DOL (Triple (O0 bl))) (D2 lt rt) = D2 (onlyL bl lt) rt
catenate' (DOR (Triple (O0 bl))) (D2 lt rt) = D2 (onlyL bl lt) rt
-- -- Case 3
catenate' (D2 lt rt) (DOL (Triple (O0 br))) = D2 lt (onlyR rt br)
catenate' (D2 lt rt) (DOR (Triple (O0 br))) = D2 lt (onlyR rt br)
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
onlyL bl      (Triple (LR ll d lr))            = Triple (LG (catenateB bl ll) d lr)
onlyL bl@B1{} (Cap (LO ll (D2 lt rt) lr) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (LY (catenateB bl ll) (D2 lt2 (cap rt cap1)) lr) cap2
onlyL bl@B1{} (Cap (LO ll (DOR ot) lr) cap1)   = Cap (LY (catenateB bl ll) (DOL ot) lr) cap1
onlyL bl      (Cap (LO ll d lr) cap1)          = Triple (LG (catenateB bl ll) (plugR d cap1) lr)
onlyL bl      (Cap (LY ll d lr) cap1)          = Triple (LG (catenateB bl ll) d2 lr) where d2 = plugL cap1 d
onlyL bl      (Triple (LG ll d lr))            = Triple (LG (catenateB bl ll) d lr)

cat0O :: Buffer q j k -> Cap OnlyTriple q i j -> Cap OnlyTriple q i k
cat0O _ (Triple O0{}) = error "Impossible"
cat0O bl@B8{} (Cap (OXO ll d lr) cap1) = case d of
  D2 lt rt ->  Cap (OXO bl (D2 (pushLeft (S1 ll) lt) rt) lr) cap1
  DOR ot -> case uncap (pushOnly (S1 ll) (cap ot cap1)) of ViewCap ot2 cap2 -> Cap (OXO bl (DOR ot2) lr) cap2
cat0O bl@B8{} (Cap (OOX ll d lr@B6{}) cap1) = case d of
  D2 lt rt -> Cap (OXO bl (D2 (pushLeft (S1 ll) lt) rt) lr) cap1
  DOR ot -> case uncap (pushOnly (S1 ll) (cap ot cap1)) of ViewCap ot2 cap2 -> Cap (OXO bl (DOR ot2) lr) cap2
cat0O bl@B8{} (Cap (OOX ll d lr@B7{}) cap1) = case d of
  D2 lt rt -> case uncap (pushLeft (S1 ll) lt) of ViewCap lt2 cap2 -> Cap (OGY bl (D2 lt2 (cap rt cap1)) lr) cap2
  DOR ot -> case uncap (pushOnly (S1 ll) (cap ot cap1)) of ViewCap ot2 cap2 -> Cap (OGY bl (DOL ot2) lr) cap2
cat0O bl@B8{} (Cap (OOX ll d lr@B8{}) cap1) =  Triple (OGG bl (push (S1 ll) (plugR d cap1)) lr)
cat0O bl@B8{} (Cap (OOX ll d lr@B9{}) cap1) =  Triple (OGG bl (push (S1 ll) (plugR d cap1)) lr)
cat0O bl@B8{} (Cap (OGY ll d lr) cap1) = case d of
  D2 lt rt -> case uncap (pushLeft (S1 ll) (cap lt cap1)) of ViewCap lt2 cap2 -> Cap (OGY bl (D2 lt2 rt) lr) cap2
  DOL ot -> case uncap (pushOnly (S1 ll) (cap ot cap1)) of ViewCap ot2 cap2 -> Cap (OGY bl (DOL ot2) lr) cap2
cat0O bl@B8{} (Cap (OYX ll d lr@B7{}) cap1) = case d of
  D2 lt rt -> case uncap (pushLeft (S1 ll) (cap lt cap1)) of ViewCap lt2 cap2 -> Cap (OGY bl (D2 lt2 rt) lr) cap2
  DOL ot -> case uncap (pushOnly (S1 ll) (cap ot cap1)) of ViewCap ot2 cap2 -> Cap (OGY bl (DOL ot2) lr) cap2
cat0O bl@B8{} (Cap (OYX ll d lr@B8{}) cap1) =  Triple $ OGG bl (push (S1 ll) (plugL cap1 d)) lr
cat0O bl@B8{} (Cap (OYX ll d lr@B9{}) cap1) =  Triple $ OGG bl (push (S1 ll) (plugL cap1 d)) lr
cat0O bl@B8{} (Triple (OGG ll d lr)) = Triple $ OGG bl (push (S1 ll) d) lr
cat0O bl@B9{} (Cap (OXO ll d lr) cap1) = case d of
  D2 lt rt ->  Cap (OXO bl (D2 (pushLeft (S1 ll) lt) rt) lr) cap1
  DOR ot -> case uncap (pushOnly (S1 ll) (cap ot cap1)) of ViewCap ot2 cap2 -> Cap (OXO bl (DOR ot2) lr) cap2
cat0O bl@B9{} (Cap (OOX ll d lr@B6{}) cap1)          = case d of
  D2 lt rt -> Cap (OXO bl (D2 (pushLeft (S1 ll) lt) rt) lr) cap1
  DOR ot -> case uncap (pushOnly (S1 ll) (cap ot cap1)) of ViewCap ot2 cap2 -> Cap (OXO bl (DOR ot2) lr) cap2
cat0O bl@B9{} (Cap (OOX ll d lr@B7{}) cap1)          = case d of
  D2 lt rt -> case uncap (pushLeft (S1 ll) lt) of ViewCap lt2 cap2 -> Cap (OGY bl (D2 lt2 (cap rt cap1)) lr) cap2
  DOR ot -> case uncap (pushOnly (S1 ll) (cap ot cap1)) of ViewCap ot2 cap2 -> Cap (OGY bl (DOL ot2) lr) cap2
cat0O bl@B9{} (Cap (OOX ll d lr@B8{}) cap1)          =  Triple (OGG bl (push (S1 ll) (plugR d cap1)) lr)
cat0O bl@B9{} (Cap (OOX ll d lr@B9{}) cap1)          =  Triple (OGG bl (push (S1 ll) (plugR d cap1)) lr)
cat0O bl@B9{} (Cap (OGY ll d lr) cap1)          = case d of
  D2 lt rt -> case uncap (pushLeft (S1 ll) (cap lt cap1)) of ViewCap lt2 cap2 -> Cap (OGY bl (D2 lt2 rt) lr) cap2
  DOL ot -> case uncap (pushOnly (S1 ll) (cap ot cap1)) of ViewCap ot2 cap2 -> Cap (OGY bl (DOL ot2) lr) cap2
cat0O bl@B9{} (Cap (OYX ll d lr@B7{}) cap1)          = case d of
  D2 lt rt -> case uncap (pushLeft (S1 ll) (cap lt cap1)) of ViewCap lt2 cap2 -> Cap (OGY bl (D2 lt2 rt) lr) cap2
  DOL ot -> case uncap (pushOnly (S1 ll) (cap ot cap1)) of ViewCap ot2 cap2 -> Cap (OGY bl (DOL ot2) lr) cap2
cat0O bl@B9{} (Cap (OYX ll d lr@B8{}) cap1)     = Triple $ OGG bl (push (S1 ll) (plugL cap1 d)) lr
cat0O bl@B9{} (Cap (OYX ll d lr@B9{}) cap1)     = Triple $ OGG bl (push (S1 ll) (plugL cap1 d)) lr
cat0O bl@B9{} (Triple (OGG ll d lr))            = Triple $ OGG bl (push (S1 ll) d) lr
cat0O bl (Cap (OXO ll d lr) cap1) = Cap (OXO (catenateB bl ll) d lr) cap1
cat0O bl@B1{} (Cap (OOX ll d lr@B6{}) cap1) = Cap (OXO (catenateB bl ll) d lr) cap1
cat0O bl@B1{} (Cap (OOX ll (D2 lt rt) lr@B7{}) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (OYX (catenateB bl ll) (D2 lt2 (cap rt cap1)) lr) cap2
cat0O bl@B1{} (Cap (OOX ll (DOR ot) lr@B7{}) cap1) = Cap (OYX (catenateB bl ll) (DOL ot) lr) cap1
cat0O bl@B1{} (Cap (OOX ll (D2 lt rt) lr@B8{}) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (OYX (catenateB bl ll) (D2 lt2 (cap rt cap1)) lr) cap2
cat0O bl@B1{} (Cap (OOX ll (DOR ot) lr@B8{}) cap1) = Cap (OYX (catenateB bl ll) (DOL ot) lr) cap1
cat0O bl@B1{} (Cap (OOX ll (D2 lt rt) lr@B9{}) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (OYX (catenateB bl ll) (D2 lt2 (cap rt cap1)) lr) cap2
cat0O bl@B1{} (Cap (OOX ll (DOR ot) lr@B9{}) cap1) = Cap (OYX (catenateB bl ll) (DOL ot) lr) cap1
cat0O bl@B2{} (Cap (OOX ll d lr@B6{}) cap1) = Cap (OXO (catenateB bl ll) d lr) cap1
cat0O bl@B2{} (Cap (OOX ll (D2 lt rt) lr@B7{}) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (OGY (catenateB bl ll) (D2 lt2 (cap rt cap1)) lr) cap2
cat0O bl@B2{} (Cap (OOX ll (DOR ot) lr@B7{}) cap1) = Cap (OGY (catenateB bl ll) (DOL ot) lr) cap1
cat0O bl@B2{} (Cap (OOX ll d lr@B8{}) cap1) = Triple (OGG (catenateB bl ll) (plugR d cap1) lr)
cat0O bl@B2{} (Cap (OOX ll d lr@B9{}) cap1) = Triple (OGG (catenateB bl ll) (plugR d cap1) lr)
cat0O bl@B3{} (Cap (OOX ll d lr@B6{}) cap1) = Cap (OXO (catenateB bl ll) d lr) cap1
cat0O bl@B3{} (Cap (OOX ll (D2 lt rt) lr@B7{}) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (OGY (catenateB bl ll) (D2 lt2 (cap rt cap1)) lr) cap2
cat0O bl@B3{} (Cap (OOX ll (DOR ot) lr@B7{}) cap1) = Cap (OGY (catenateB bl ll) (DOL ot) lr) cap1
cat0O bl@B3{} (Cap (OOX ll d lr@B8{}) cap1) = Triple (OGG (catenateB bl ll) (plugR d cap1) lr)
cat0O bl@B3{} (Cap (OOX ll d lr@B9{}) cap1) = Triple (OGG (catenateB bl ll) (plugR d cap1) lr)
cat0O bl@B4{} (Cap (OOX ll d lr@B6{}) cap1) = Cap (OXO (catenateB bl ll) d lr) cap1
cat0O bl@B4{} (Cap (OOX ll (D2 lt rt) lr@B7{}) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (OGY (catenateB bl ll) (D2 lt2 (cap rt cap1)) lr) cap2
cat0O bl@B4{} (Cap (OOX ll (DOR ot) lr@B7{}) cap1) = Cap (OGY (catenateB bl ll) (DOL ot) lr) cap1
cat0O bl@B4{} (Cap (OOX ll d lr@B8{}) cap1) = Triple (OGG (catenateB bl ll) (plugR d cap1) lr)
cat0O bl@B4{} (Cap (OOX ll d lr@B9{}) cap1) = Triple (OGG (catenateB bl ll) (plugR d cap1) lr)
cat0O bl@B5{} (Cap (OOX ll d lr@B6{}) cap1) = Cap (OXO (catenateB bl ll) d lr) cap1
cat0O bl@B5{} (Cap (OOX ll (D2 lt rt) lr@B7{}) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (OGY (catenateB bl ll) (D2 lt2 (cap rt cap1)) lr) cap2
cat0O bl@B5{} (Cap (OOX ll (DOR ot) lr@B7{}) cap1) = Cap (OGY (catenateB bl ll) (DOL ot) lr) cap1
cat0O bl@B5{} (Cap (OOX ll d lr@B8{}) cap1) = Triple (OGG (catenateB bl ll) (plugR d cap1) lr)
cat0O bl@B5{} (Cap (OOX ll d lr@B9{}) cap1) = Triple (OGG (catenateB bl ll) (plugR d cap1) lr)
cat0O bl@B6{} (Cap (OOX ll d lr@B6{}) cap1) = Cap (OXO (catenateB bl ll) d lr) cap1
cat0O bl@B6{} (Cap (OOX ll (D2 lt rt) lr@B7{}) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (OGY (catenateB bl ll) (D2 lt2 (cap rt cap1)) lr) cap2
cat0O bl@B6{} (Cap (OOX ll (DOR ot) lr@B7{}) cap1) = Cap (OGY (catenateB bl ll) (DOL ot) lr) cap1
cat0O bl@B6{} (Cap (OOX ll d lr@B8{}) cap1) = Triple (OGG (catenateB bl ll) (plugR d cap1) lr)
cat0O bl@B6{} (Cap (OOX ll d lr@B9{}) cap1) = Triple (OGG (catenateB bl ll) (plugR d cap1) lr)
cat0O bl@B7{} (Cap (OOX ll d lr@B6{}) cap1) = Cap (OXO (catenateB bl ll) d lr) cap1
cat0O bl@B7{} (Cap (OOX ll (D2 lt rt) lr@B7{}) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (OGY (catenateB bl ll) (D2 lt2 (cap rt cap1)) lr) cap2
cat0O bl@B7{} (Cap (OOX ll (DOR ot) lr@B7{}) cap1) = Cap (OGY (catenateB bl ll) (DOL ot) lr) cap1
cat0O bl@B7{} (Cap (OOX ll d lr@B8{}) cap1) = Triple (OGG (catenateB bl ll) (plugR d cap1) lr)
cat0O bl@B7{} (Cap (OOX ll d lr@B9{}) cap1) = Triple (OGG (catenateB bl ll) (plugR d cap1) lr)
cat0O bl (Cap (OGY ll d lr) cap1) = Cap (OGY (catenateB bl ll) d lr) cap1
cat0O bl (Cap (OYX ll d lr@B7{}) cap1) = Cap (OGY (catenateB bl ll) d lr) cap1
cat0O bl (Cap (OYX ll d lr@B8{}) cap1) = Triple (OGG (catenateB bl ll) (plugL cap1 d) lr)
cat0O bl (Cap (OYX ll d lr@B9{}) cap1) = Triple (OGG (catenateB bl ll) (plugL cap1 d) lr)
cat0O bl (Triple (OGG ll d lr)) = Triple (OGG (catenateB bl ll) d lr)

catO0 :: Cap OnlyTriple q j k -> Buffer q i j -> Cap OnlyTriple q i k
catO0 (Triple O0{}) _ = error "Impossible"
catO0 (Cap (OOX rl d rr) cap1) br@B8{} = case d of
  D2 lt rt -> case uncap (injectRight (cap rt cap1) (S1 rr)) of ViewCap rt2 cap2 -> Cap (OOX rl (D2 lt rt2) br) cap2
  DOR ot -> case uncap (injectOnly (cap ot cap1) (S1 rr)) of ViewCap ot2 cap2 -> Cap (OOX rl (DOR ot2) br) cap2
catO0 (Cap (OXO rl@B7{} d rr) cap1) br@B8{} = case d of
  D2 lt rt -> case uncap lt of ViewCap lt2 cap2 -> Cap (OYX rl (D2 lt2 (injectRight (cap rt cap1) (S1 rr))) br) cap2
  DOR ot -> case uncap (injectOnly (cap ot cap1) (S1 rr)) of ViewCap ot2 cap2 -> Cap (OYX rl (DOL ot2) br) cap2
catO0 (Cap (OXO rl@B8{} d rr) cap1) br@B8{} = case d of
  D2 lt rt -> Triple (OGG rl (D2 lt (injectRight (cap rt cap1) (S1 rr))) br)
  DOR ot -> Triple (OGG rl (DOL (injectOnly (cap ot cap1) (S1 rr))) br)
catO0 (Cap (OXO rl@B9{} d rr) cap1) br@B8{} = case d of
  D2 lt rt -> Triple (OGG rl (D2 lt (injectRight (cap rt cap1) (S1 rr))) br)
  DOR ot -> Triple (OGG rl (DOL (injectOnly (cap ot cap1) (S1 rr))) br)
catO0 (Cap (OYX rl d rr) cap1) br@B8{} = case d of
  D2 lt rt -> injectRight rt (S1 rr) $ \e -> Cap (OYX rl (D2 lt e) br) cap1
  DOL ot -> case uncap (injectOnly (cap ot cap1) (S1 rr)) of ViewCap ot2 cap2 -> Cap (OYX rl (DOL ot2) br) cap2
catO0 (Cap (OGY rl d rr) cap1) br@B8{} = case d of
  D2 lt rt -> injectRight rt (S1 rr) $ \e -> Triple (OGG rl (D2 (cap lt cap1) e) br)
  DOL ot -> Triple (OGG rl (DOL (injectOnly (cap ot cap1) (S1 rr))) br)
catO0 (Triple (OGG rl d rr)) br@B8{} = case d of
  D2 lt rt -> injectRight rt (S1 rr) $ \e -> Triple (OGG rl (D2 lt e) br)
  DOL ot -> injectOnly ot (S1 rr) $ \e -> Triple (OGG rl (DOL e) br)
  DOR ot -> injectOnly ot (S1 rr) $ \e -> Triple (OGG rl (DOL e) br)
  D0 -> Triple (OGG rl (DOL (Triple (O0 (B1 (S1 rr))))) br)
catO0 (Cap (OOX rl d rr) cap1) br@B9{} = case d of
  D2 lt rt -> case uncap (injectRight (cap rt cap1) (S1 rr)) of ViewCap rt2 cap2 -> Cap (OOX rl (D2 lt rt2) br) cap2
  DOR ot -> case uncap (injectOnly (cap ot cap1) (S1 rr)) of ViewCap ot2 cap2 -> Cap (OOX rl (DOR ot2) br) cap2
catO0 (Cap (OXO rl@B7{} d rr) cap1) br@B9{} = case d of
  D2 lt rt -> case uncap lt of ViewCap lt2 cap2 -> Cap (OYX rl (D2 lt2 (injectRight (cap rt cap1) (S1 rr))) br) cap2
  DOR ot -> case uncap (injectOnly (cap ot cap1) (S1 rr)) of ViewCap ot2 cap2 -> Cap (OYX rl (DOL ot2) br) cap2
catO0 (Cap (OXO rl@B8{} d rr) cap1) br@B9{} = case d of
  D2 lt rt -> Triple (OGG rl (D2 lt (injectRight (cap rt cap1) (S1 rr))) br)
  DOR ot -> Triple (OGG rl (DOL (injectOnly (cap ot cap1) (S1 rr))) br)
catO0 (Cap (OXO rl@B9{} d rr) cap1) br@B9{} = case d of
  D2 lt rt -> Triple (OGG rl (D2 lt (injectRight (cap rt cap1) (S1 rr))) br)
  DOR ot -> Triple (OGG rl (DOL (injectOnly (cap ot cap1) (S1 rr))) br)
catO0 (Cap (OYX rl d rr) cap1) br@B9{} = case d of
  D2 lt rt -> injectRight rt (S1 rr) $ \e -> Cap (OYX rl (D2 lt e) br) cap1
  DOL ot -> case uncap (injectOnly (cap ot cap1) (S1 rr)) of ViewCap ot2 cap2 -> Cap (OYX rl (DOL ot2) br) cap2
catO0 (Cap (OGY rl d rr) cap1) br@B9{} = case d of
  D2 lt rt -> injectRight rt (S1 rr) $ \e -> Triple (OGG rl (D2 (cap lt cap1) e) br)
  DOL ot -> Triple (OGG rl (DOL (injectOnly (cap ot cap1) (S1 rr))) br)
catO0 (Triple (OGG rl d rr)) br@B9{} = case d of
  D2 lt rt -> injectRight rt (S1 rr) $ \e -> Triple (OGG rl (D2 lt e) br)
  DOL ot -> injectOnly ot (S1 rr) $ \e -> Triple (OGG rl (DOL e) br)
  DOR ot -> injectOnly ot (S1 rr) $ \e -> Triple (OGG rl (DOL e) br)
  D0 -> Triple (OGG rl (DOL (Triple (O0 (B1 (S1 rr))))) br)
catO0 (Cap (OOX rl d rr) cap1) br = Cap (OOX rl d (catenateB rr br)) cap1
catO0 (Cap (OXO rl@B7{} d rr) cap1) br = case d of
  D2 lt rt -> case uncap lt of ViewCap lt2 cap2 -> Cap (OYX rl (D2 lt2 (cap rt cap1)) (catenateB rr br)) cap2
  DOR ot -> Cap (OYX rl (DOL ot) (catenateB rr br)) cap1
catO0 (Cap (OXO rl@B8{} d rr) cap1) br@B1{} = case d of
  D2 lt rt -> case uncap lt of ViewCap lt2 cap2 -> Cap (OGY rl (D2 lt2 (cap rt cap1)) (catenateB rr br)) cap2
  DOR ot -> Cap (OGY rl (DOL ot) (catenateB rr br)) cap1
catO0 (Cap (OXO rl@B8{} d rr) cap1) br@B2{} = Triple (OGG rl (plugR d cap1) (catenateB rr br))
catO0 (Cap (OXO rl@B8{} d rr) cap1) br@B3{} = Triple (OGG rl (plugR d cap1) (catenateB rr br))
catO0 (Cap (OXO rl@B8{} d rr) cap1) br@B4{} = Triple (OGG rl (plugR d cap1) (catenateB rr br))
catO0 (Cap (OXO rl@B8{} d rr) cap1) br@B5{} = Triple (OGG rl (plugR d cap1) (catenateB rr br))
catO0 (Cap (OXO rl@B8{} d rr) cap1) br@B6{} = Triple (OGG rl (plugR d cap1) (catenateB rr br))
catO0 (Cap (OXO rl@B8{} d rr) cap1) br@B7{} = Triple (OGG rl (plugR d cap1) (catenateB rr br))
catO0 (Cap (OXO rl@B9{} d rr) cap1) br@B1{} = case d of
  D2 lt rt -> case uncap lt of ViewCap lt2 cap2 -> Cap (OGY rl (D2 lt2 (cap rt cap1)) (catenateB rr br)) cap2
  DOR ot -> Cap (OGY rl (DOL ot) (catenateB rr br)) cap1
catO0 (Cap (OXO rl@B9{} d rr) cap1) br@B2{} = Triple (OGG rl (plugR d cap1) (catenateB rr br))
catO0 (Cap (OXO rl@B9{} d rr) cap1) br@B3{} = Triple (OGG rl (plugR d cap1) (catenateB rr br))
catO0 (Cap (OXO rl@B9{} d rr) cap1) br@B4{} = Triple (OGG rl (plugR d cap1) (catenateB rr br))
catO0 (Cap (OXO rl@B9{} d rr) cap1) br@B5{} = Triple (OGG rl (plugR d cap1) (catenateB rr br))
catO0 (Cap (OXO rl@B9{} d rr) cap1) br@B6{} = Triple (OGG rl (plugR d cap1) (catenateB rr br))
catO0 (Cap (OXO rl@B9{} d rr) cap1) br@B7{} = Triple (OGG rl (plugR d cap1) (catenateB rr br))
catO0 (Cap (OYX rl d rr) cap1) br = Cap (OYX rl d (catenateB rr br)) cap1
catO0 (Cap (OGY rl d rr) cap1) br = Triple (OGG rl (plugL cap1 d) (catenateB rr br))
catO0 (Triple (OGG rl d rr)) br = Triple (OGG rl d (catenateB rr br))

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
onlyR (Triple (RR rl d rr))            br      = Triple (RG rl d (catenateB rr br))
onlyR (Cap (RO rl (D2 lt rt) rr) cap1) br@B1{} = case uncap lt of ViewCap lt2 cap2 -> Cap (RY rl (D2 lt2 (cap rt cap1)) (catenateB rr br)) cap2
onlyR (Cap (RO rl (DOR ot) rr) cap1)   br@B1{} = Cap (RY rl (DOL ot) (catenateB rr br)) cap1
onlyR (Cap (RO rl d rr) cap1)          br      = Triple (RG rl (plugR d cap1) (catenateB rr br))
onlyR (Cap (RY rl d rr) cap1)          br      = Triple (RG rl d2 (catenateB rr br)) where d2 = plugL cap1 d
onlyR (Triple (RG rl d rr))            br      = Triple (RG rl d (catenateB rr br))

fixLeft :: Deque q i j -> Cap LeftTriple q i j
fixLeft d = case d of
  D0 -> error "Impossible"
  DOL c -> only c
  DOR c -> only c
  D2 (Triple (LG p1 D0 s1)) (Triple (R0 p2 s2@B9{})) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  D2 (Triple (LG p1 D0 s1)) (Triple (R0 p2 s2@B8{})) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  D2 (Triple (LG p1 D0 s1)) (Triple (R0 p2 s2))      -> only (Triple (O0 (catenateB (catenateB (catenateB p1 s1) p2) s2)))
  D2 (Triple (LG p1 D0 s1)) (Triple (RG p2 d2 s2))   -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) d2 s2))
  D2 (Triple (LG p1 D0 s1)) (Triple (RR p2 d2 s2))   -> only (Triple (OXR (catenateB (catenateB p1 s1) p2) d2 s2))
  D2 (Triple (LG p1 D0 s1)) (Cap (RO p2 d2 s2) c)    -> only (Cap (OXO (catenateB (catenateB p1 s1) p2) d2 s2) c)
  D2 (Triple (LG p1 D0 s1)) (Cap (RY p2 d2 s2) c)    -> only (Cap (OGY (catenateB (catenateB p1 s1) p2) d2 s2) c)
  D2 (Triple (L0 p1 s1)) (Triple (R0 p2 s2@B9{}))    -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  D2 (Triple (L0 p1 s1)) (Triple (R0 p2 s2@B8{}))    -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  D2 (Triple (L0 p1 s1)) (Triple (R0 p2 s2))         -> only (Triple (O0 (catenateB (catenateB (catenateB p1 s1) p2) s2)))
  D2 (Triple (L0 p1 s1)) (Triple (RG p2 d2 s2))      -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) d2 s2))
  D2 (Triple (L0 p1 s1)) (Triple (RR p2 d2 s2))      -> only (Triple (OXR (catenateB (catenateB p1 s1) p2) d2 s2))
  D2 (Triple (L0 p1 s1)) (Cap (RO p2 d2 s2) c)       -> only (Cap (OXO (catenateB (catenateB p1 s1) p2) d2 s2) c)
  D2 (Triple (L0 p1 s1)) (Cap (RY p2 d2 s2) c)       -> only (Cap (OGY (catenateB (catenateB p1 s1) p2) d2 s2) c)
  D2 (Triple (LG p1 d1 s1)) (Triple (RG p2 d2 s2)) -> case aux s2 of H rem2 r2 -> Triple $ LG p1 (inject d1 (S3 (catenateB s1 p2) d2 rem2)) r2
  D2 (Triple (LG p1 d1 s1)) (Triple (RR p2 d2 s2)) -> case aux s2 of H rem2 r2 -> Triple $ LG p1 (inject d1 (S3 (catenateB s1 p2) d2 rem2)) r2
  D2 (Triple (LG p1 d1 s1)) (Triple (R0 p2 s2))    -> case aux s2 of H rem2 r2 -> Triple $ LG p1 (inject d1 (S3 (catenateB s1 p2) D0 rem2)) r2
  D2 (Triple (LG p1 d1 s1)) (Cap (RY p2 d2 s2) c)  -> case aux s2 of H rem2 r2 -> Triple $ LG p1 (inject d1 (S3 (catenateB s1 p2) (plugL c d2) rem2)) r2
  D2 (Triple (LG p1 d1 s1)) (Cap (RO p2 d2 s2) c)  -> case aux s2 of H rem2 r2 -> Triple $ LG p1 (inject d1 (S3 (catenateB s1 p2) (plugR d2 c) rem2)) r2
  D2 (Triple (LR p1 d1 s1)) (Triple (RG p2 d2 s2)) -> case aux s2 of H rem2 r2 -> Triple $ LR p1 (inject d1 (S3 (catenateB s1 p2) d2 rem2)) r2
  D2 (Triple (LR p1 d1 s1)) (Triple (RR p2 d2 s2)) -> case aux s2 of H rem2 r2 -> Triple $ LR p1 (inject d1 (S3 (catenateB s1 p2) d2 rem2)) r2
  D2 (Triple (LR p1 d1 s1)) (Triple (R0 p2 s2))    -> case aux s2 of H rem2 r2 -> Triple $ LR p1 (inject d1 (S3 (catenateB s1 p2) D0 rem2)) r2
  D2 (Triple (LR p1 d1 s1)) (Cap (RY p2 d2 s2) c)  -> case aux s2 of H rem2 r2 -> Triple $ LR p1 (inject d1 (S3 (catenateB s1 p2) (plugL c d2) rem2)) r2
  D2 (Triple (LR p1 d1 s1)) (Cap (RO p2 d2 s2) c)  -> case aux s2 of H rem2 r2 -> Triple $ LR p1 (inject d1 (S3 (catenateB s1 p2) (plugR d2 c) rem2)) r2
  D2 (Cap (LY p1 d1 s1) cl) (Triple (RG p2 d2 s2)) -> case aux s2 of
    H rem2 r2 -> case d1 of
      D2 d1l d1r -> Cap (LY p1 (D2 d1l (injectRight d1r (S3 (catenateB s1 p2) d2 rem2))) r2) cl
      DOL ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) d2 rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) r2) c2
  D2 (Cap (LY p1 d1 s1) cl) (Triple (RR p2 d2 s2)) -> case aux s2 of
    H rem2 r2 -> case d1 of
      D2 d1l d1r -> Cap (LY p1 (D2 d1l (injectRight d1r (S3 (catenateB s1 p2) d2 rem2))) r2) cl
      DOL ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) d2 rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) r2) c2
  D2 (Cap (LY p1 d1 s1) cl) (Triple (R0 p2 s2)) -> case aux s2 of
    H rem2 r2 -> case d1 of
      D2 d1l d1r -> Cap (LY p1 (D2 d1l (injectRight d1r (S3 (catenateB s1 p2) D0 rem2))) r2) cl
      DOL ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) D0 rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) r2) c2
  D2 (Cap (LY p1 d1 s1) cl) (Cap (RY p2 d2 s2) c) -> case aux s2 of
    H rem2 r2 -> case d1 of
      D2 d1l d1r -> Cap (LY p1 (D2 d1l (injectRight d1r (S3 (catenateB s1 p2) (plugL c d2) rem2))) r2) cl
      DOL ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) (plugL c d2) rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) r2) c2
  D2 (Cap (LY p1 d1 s1) cl) (Cap (RO p2 d2 s2) c) -> case aux s2 of
    H rem2 r2 -> case d1 of
      D2 d1l d1r -> Cap (LY p1 (D2 d1l (injectRight d1r (S3 (catenateB s1 p2) (plugR d2 c) rem2))) r2) cl
      DOL ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) (plugR d2 c) rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) r2) c2
  D2 (Cap (LO p1 d1 s1) cl) (Triple (RG p2 d2 s2)) -> case aux s2 of
    H rem2 r2 -> case d1 of
      D2 d1l d1r -> case uncap (injectRight (cap d1r cl) (S3 (catenateB s1 p2) d2 rem2)) of ViewCap d1r' c2 -> Cap (LO p1 (D2 d1l d1r') r2) c2
      DOR ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) d2 rem2)) of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) r2) c2
  D2 (Cap (LO p1 d1 s1) cl) (Triple (RR p2 d2 s2)) -> case aux s2 of
    H rem2 r2 -> case d1 of
      D2 d1l d1r -> case uncap (injectRight (cap d1r cl) (S3 (catenateB s1 p2) d2 rem2)) of ViewCap d1r' c2 -> Cap (LO p1 (D2 d1l d1r') r2) c2
      DOR ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) d2 rem2)) of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) r2) c2
  D2 (Cap (LO p1 d1 s1) cl) (Triple (R0 p2 s2)) -> case aux s2 of
    H rem2 r2 -> case d1 of
      D2 d1l d1r -> case uncap (injectRight (cap d1r cl) (S3 (catenateB s1 p2) D0 rem2)) of ViewCap d1r' c2 -> Cap (LO p1 (D2 d1l d1r') r2) c2
      DOR ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) D0 rem2)) of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) r2) c2
  D2 (Cap (LO p1 d1 s1) cl) (Cap (RY p2 d2 s2) c) -> case aux s2 of
    H rem2 r2 -> case d1 of
      D2 d1l d1r -> case uncap (injectRight (cap d1r cl) (S3 (catenateB s1 p2) (plugL c d2) rem2)) of ViewCap d1r' c2 -> Cap (LO p1 (D2 d1l d1r') r2) c2
      DOR ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) (plugL c d2) rem2)) of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) r2) c2
  D2 (Cap (LO p1 d1 s1) cl) (Cap (RO p2 d2 s2) c) -> case aux s2 of
    H rem2 r2 -> case d1 of
      D2 d1l d1r -> case uncap (injectRight (cap d1r cl) (S3 (catenateB s1 p2) (plugR d2 c) rem2)) of ViewCap d1r' c2 -> Cap (LO p1 (D2 d1l d1r') r2) c2
      DOR ot -> case uncap (injectOnly (cap ot cl) (S3 (catenateB s1 p2) (plugR d2 c) rem2)) of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) r2) c2
  where
    aux :: Buffer q i l -> HPair (Buffer q) (Buffer q) i l
    aux s2 = case ejectB s2 of
      H srem1 s2r1 -> case ejectB (shiftless srem1) of
        H srem2 s2r2 -> H (shiftless srem2) (B2 s2r2 s2r1)

    only :: Cap OnlyTriple q i j -> Cap LeftTriple q i j
    only (Triple O0{}) = error "Impossible"
    only (Triple (OGG p1 D0 s1)) = onlyPS p1 s1
    only (Triple (ORX p1 D0 s1)) = onlyPS p1 s1
    only (Triple (OXR p1 D0 s1)) = onlyPS p1 s1
    only (Triple (OGG p1 d1 s1)) = case aux s1 of
      H rem2 r2 -> Triple $ LG p1 (inject d1 (S1 rem2)) r2
    only (Triple (ORX p1 d1 s1)) = case aux s1 of
      H rem2 r2 -> Triple $ LR p1 (inject d1 (S1 rem2)) r2
    only (Triple (OXR p1@B6{} d1 s1)) = case aux s1 of
      H rem2 r2 -> case inject d1 (S1 rem2) of
        D0 -> error "Impossible"
        D2 lt rt -> case uncap rt of ViewCap rt2 c2 -> Cap (LO p1 (D2 lt rt2) r2) c2
        DOL ot -> case uncap ot of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) r2) c2
        DOR ot -> case uncap ot of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) r2) c2
    only (Triple (OXR p1@B7{} d1 s1)) = case aux s1 of
      H rem2 r2 -> case inject d1 (S1 rem2) of
        D0 -> error "Impossible"
        D2 lt rt -> case uncap lt of ViewCap lt2 c2 -> Cap (LY p1 (D2 lt2 rt) r2) c2
        DOL ot -> case uncap ot of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) r2) c2
        DOR ot -> case uncap ot of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) r2) c2
    only (Triple (OXR p1@B8{} d1 s1)) = case aux s1 of H rem2 r2 -> Triple $ LG p1 (inject d1 (S1 rem2)) r2
    only (Triple (OXR p1@B9{} d1 s1)) = case aux s1 of H rem2 r2 -> Triple $ LG p1 (inject d1 (S1 rem2)) r2
    only (Cap (OOX p1 d1 s1) c) = case aux s1 of
      H rem2 r2 -> case plugR d1 c of -- (S1 rem2) foo
        D2 lt rt -> case uncap $ injectRight rt (S1 rem2) of ViewCap rt3 c3 -> Cap (LO p1 (D2 lt rt3) r2) c3
        DOL ot -> case uncap $ injectOnly ot (S1 rem2) of ViewCap ot3 c3 -> Cap (LO p1 (DOR ot3) r2) c3
        DOR ot -> case uncap $ injectOnly ot (S1 rem2) of ViewCap ot3 c3 -> Cap (LO p1 (DOR ot3) r2) c3
        D0 -> error "Impossible"
    only (Cap (OXO p1@B7{} d1 s1) c) = case aux s1 of
      H rem2 r2 -> case inject (plugR d1 c) (S1 rem2) of
        D2 lt rt -> case uncap lt of ViewCap lt2 c2 -> Cap (LY p1 (D2 lt2 rt) r2) c2
        DOL ot -> case uncap ot of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) r2) c2
        DOR ot -> case uncap ot of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) r2) c2
        D0 -> error "Impossible"
    only (Cap (OXO p1@B8{} d1 s1) c) = case aux s1 of H rem2 r2 -> Triple (LG p1 (inject (plugR d1 c) (S1 rem2)) r2)
    only (Cap (OXO p1@B9{} d1 s1) c) = case aux s1 of H rem2 r2 -> Triple (LG p1 (inject (plugR d1 c) (S1 rem2)) r2)
    only (Cap (OYX p1 d1 s1) c) = case aux s1 of
      H rem2 r2 -> case plugL c d1 of
        D2 lt rt -> case uncap lt of ViewCap lt2 c2 -> Cap (LY p1 (D2 lt2 (injectRight rt (S1 rem2))) r2) c2
        DOL ot -> case uncap (injectOnly ot (S1 rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) r2) c2
        DOR _ -> error "Impossible"
        D0 -> error "Impossible"
    only (Cap (OGY p1 d1 s1) c) = case aux s1 of
      H rem2 r2 -> case plugL c d1 of
        D2 lt rt -> Triple (LG p1 (D2 lt (injectRight rt (S1 rem2))) r2)
        DOL ot -> Triple (LG p1 (DOL (injectOnly ot (S1 rem2))) r2)
        DOR _ -> error "Impossible"
        D0 -> error "Impossible"

    onlyPS :: Buffer q j' j -> Buffer q i j' -> Cap LeftTriple q i j
    onlyPS p1 s1@B9{} = case popB s1 of
        H s1l1 srem1 -> case popB (shiftless srem1) of
          H s1l2 srem2 -> case popB (shiftless srem2) of
            H s1l3 srem3 -> case aux (shiftless srem3) of
              H rem5 s2 -> Triple $ LG (injectB (injectB (injectB p1 s1l1) s1l2) s1l3) (push (S1 rem5) D0) s2

    onlyPS p1 s1 = case ejectB s1 of
      H srem1 s1r1 -> case ejectB (shiftless srem1) of
        H srem2 s1r2 -> Triple $ LG (catenateB p1 (shiftless srem2)) D0 (B2 s1r2 s1r1)

fixRight :: Deque q i j -> Cap RightTriple q i j
fixRight d = case d of
  D0 -> error "Impossible"
  DOL c -> only c
  DOR c -> only c
  D2 (Triple (L0 p2@B9{} s2)) (Triple (RG p1 D0 s1)) -> only (Triple (OGG p2 D0 (catenateB s2 (catenateB p1 s1))))
  D2 (Triple (L0 p2@B8{} s2)) (Triple (RG p1 D0 s1)) -> only (Triple (OGG p2 D0 (catenateB s2 (catenateB p1 s1))))
  D2 (Triple (L0 p2 s2)) (Triple (RG p1 D0 s1)) -> only (Triple (O0 (catenateB p2 (catenateB s2 (catenateB p1 s1)))))
  D2 (Triple (LG p2 d2 s2)) (Triple (RG p1 D0 s1)) -> only (Triple (OGG p2 d2 (catenateB s2 (catenateB p1 s1))))
  D2 (Triple (LR p2 d2 s2)) (Triple (RG p1 D0 s1)) -> only (Triple (ORX p2 d2 (catenateB s2 (catenateB p1 s1))))
  D2 (Cap (LO p2 d2 s2) c) (Triple (RG p1 D0 s1)) -> only (Cap (OOX p2 d2 (catenateB (catenateB s2 p1) s1)) c)
  D2 (Cap (LY p2 d2 s2) c) (Triple (RG p1 D0 s1)) -> only (Cap (OYX p2 d2 (catenateB (catenateB s2 p1) s1)) c)
  D2 (Triple (L0 p2@B9{} s2)) (Triple (R0 p1 s1)) -> only (Triple (OGG p2 D0 (catenateB s2 (catenateB p1 s1))))
  D2 (Triple (L0 p2@B8{} s2)) (Triple (R0 p1 s1)) -> only (Triple (OGG p2 D0 (catenateB s2 (catenateB p1 s1))))
  D2 (Triple (L0 p2 s2)) (Triple (R0 p1 s1)) -> only (Triple (O0 (catenateB p2 (catenateB s2 (catenateB p1 s1)))))
  D2 (Triple (LG p2 d2 s2)) (Triple (R0 p1 s1)) -> only (Triple (OGG p2 d2 (catenateB s2 (catenateB p1 s1))))
  D2 (Triple (LR p2 d2 s2)) (Triple (R0 p1 s1)) -> only (Triple (ORX p2 d2 (catenateB s2 (catenateB p1 s1))))
  D2 (Cap (LO p2 d2 s2) c) (Triple (R0 p1 s1)) -> only (Cap (OOX p2 d2 (catenateB (catenateB s2 p1) s1)) c)
  D2 (Cap (LY p2 d2 s2) c) (Triple (R0 p1 s1)) -> only (Cap (OYX p2 d2 (catenateB (catenateB s2 p1) s1)) c)
  D2 (Triple (LG p2 d2 s2)) (Triple (RG p1 d1 s1)) -> case aux p2 of H l2 rem2 -> Triple $ RG l2 (push (S3 rem2 d2 (catenateB s2 p1)) d1) s1
  D2 (Triple (LR p2 d2 s2)) (Triple (RG p1 d1 s1)) -> case aux p2 of H l2 rem2 -> Triple $ RG l2 (push (S3 rem2 d2 (catenateB s2 p1)) d1) s1
  D2 (Triple (L0 p2 s2)) (Triple (RG p1 d1 s1)) -> case aux p2 of H l2 rem2 -> Triple $ RG l2 (push (S3 rem2 D0 (catenateB s2 p1)) d1) s1
  D2 (Cap (LY p2 d2 s2) c) (Triple (RG p1 d1 s1))  -> case aux p2 of H l2 rem2 -> Triple $ RG l2 (push (S3 rem2 (plugL c d2) (catenateB s2 p1)) d1) s1
  D2 (Cap (LO p2 d2 s2) c) (Triple (RG p1 d1 s1)) -> case aux p2 of H l2 rem2 -> Triple $ RG l2 (push (S3 rem2 (plugR d2 c) (catenateB s2 p1)) d1) s1
  D2 (Triple (LG p2 d2 s2)) (Triple (RR p1 d1 s1)) -> case aux p2 of H l2 rem2 -> Triple $ RR l2 (push (S3 rem2 d2 (catenateB s2 p1)) d1) s1
  D2 (Triple (LR p2 d2 s2)) (Triple (RR p1 d1 s1)) -> case aux p2 of H l2 rem2 -> Triple $ RR l2 (push (S3 rem2 d2 (catenateB s2 p1)) d1) s1
  D2 (Triple (L0 p2 s2)) (Triple (RR p1 d1 s1)) -> case aux p2 of H l2 rem2 -> Triple $ RR l2 (push (S3 rem2 D0 (catenateB s2 p1)) d1) s1
  D2 (Cap (LY p2 d2 s2) c) (Triple (RR p1 d1 s1)) -> case aux p2 of H l2 rem2 -> Triple $ RR l2 (push (S3 rem2 (plugL c d2) (catenateB s2 p1)) d1) s1
  D2 (Cap (LO p2 d2 s2) c) (Triple (RR p1 d1 s1)) -> case aux p2 of H l2 rem2 -> Triple $ RR l2 (push (S3 rem2 (plugR d2 c) (catenateB s2 p1)) d1) s1
  D2 (Triple (LG p2 d2 s2)) (Cap (RO p1 d1 s1) cl) -> case aux p2 of
    H l2 rem2 -> case d1 of
      D2 d1l d1r -> Cap (RO l2 (D2 (pushLeft (S3 rem2 d2 (catenateB s2 p1)) d1l) d1r) s1) cl
      DOR ot -> case uncap (pushOnly (S3 rem2 d2 (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RO l2 (DOR ot2) s1) c2
  D2 (Triple (LR p2 d2 s2)) (Cap (RO p1 d1 s1) cl) -> case aux p2 of
    H l2 rem2 -> case d1 of
      D2 d1l d1r -> Cap (RO l2 (D2 (pushLeft (S3 rem2 d2 (catenateB s2 p1)) d1l) d1r) s1) cl
      DOR ot -> case uncap (pushOnly (S3 rem2 d2 (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RO l2 (DOR ot2) s1) c2
  D2 (Triple (L0 p2 s2)) (Cap (RO p1 d1 s1) cl) -> case aux p2 of
    H l2 rem2 -> case d1 of
      D2 d1l d1r -> Cap (RO l2 (D2 (pushLeft (S3 rem2 D0 (catenateB s2 p1)) d1l) d1r) s1) cl
      DOR ot -> case uncap (pushOnly (S3 rem2 D0 (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RO l2 (DOR ot2) s1) c2
  D2 (Cap (LY p2 d2 s2) cr) (Cap (RO p1 d1 s1) cl) -> case aux p2 of
    H l2 rem2 -> case d1 of
      D2 d1l d1r -> Cap (RO l2 (D2 (pushLeft (S3 rem2 (plugL cr d2) (catenateB s2 p1)) d1l) d1r) s1) cl
      DOR ot -> case uncap (pushOnly (S3 rem2 (plugL cr d2) (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RO l2 (DOR ot2) s1) c2
  D2 (Cap (LO p2 d2 s2) cr) (Cap (RO p1 d1 s1) cl) -> case aux p2 of
    H l2 rem2 -> case d1 of
      D2 d1l d1r -> Cap (RO l2 (D2 (pushLeft (S3 rem2 (plugR d2 cr) (catenateB s2 p1)) d1l) d1r) s1) cl
      DOR ot -> case uncap (pushOnly (S3 rem2 (plugR d2 cr) (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RO l2 (DOR ot2) s1) c2
  D2 (Triple (LG p2 d2 s2)) (Cap (RY p1 d1 s1) cl) -> case aux p2 of
    H l2 rem2 -> case d1 of
      D2 d1l d1r -> case uncap (pushLeft (S3 rem2 d2 (catenateB s2 p1)) (cap d1l cl)) of ViewCap d1l' c2 -> Cap (RY l2 (D2 d1l' d1r) s1) c2
      DOL ot -> case uncap (pushOnly (S3 rem2 d2 (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RY l2 (DOL ot2) s1) c2
  D2 (Triple (LR p2 d2 s2)) (Cap (RY p1 d1 s1) cl) -> case aux p2 of
    H l2 rem2 -> case d1 of
      D2 d1l d1r -> case uncap (pushLeft (S3 rem2 d2 (catenateB s2 p1)) (cap d1l cl)) of ViewCap d1l' c2 -> Cap (RY l2 (D2 d1l' d1r) s1) c2
      DOL ot -> case uncap (pushOnly (S3 rem2 d2 (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RY l2 (DOL ot2) s1) c2
  D2 (Triple (L0 p2 s2)) (Cap (RY p1 d1 s1) cl) -> case aux p2 of
    H l2 rem2 -> case d1 of
      D2 d1l d1r -> case uncap (pushLeft (S3 rem2 D0 (catenateB s2 p1)) (cap d1l cl)) of ViewCap d1l' c2 -> Cap (RY l2 (D2 d1l' d1r) s1) c2
      DOL ot -> case uncap (pushOnly (S3 rem2 D0 (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RY l2 (DOL ot2) s1) c2
  D2 (Cap (LY p2 d2 s2) cr) (Cap (RY p1 d1 s1) cl) -> case aux p2 of
    H l2 rem2 -> case d1 of
      D2 d1l d1r -> case uncap (pushLeft (S3 rem2 (plugL cr d2) (catenateB s2 p1)) (cap d1l cl)) of ViewCap d1l' c2 -> Cap (RY l2 (D2 d1l' d1r) s1) c2
      DOL ot -> case uncap (pushOnly (S3 rem2 (plugL cr d2) (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RY l2 (DOL ot2) s1) c2
  D2 (Cap (LO p2 d2 s2) cr) (Cap (RY p1 d1 s1) cl) -> case aux p2 of
    H l2 rem2 -> case d1 of
      D2 d1l d1r -> case uncap (pushLeft (S3 rem2 (plugR d2 cr) (catenateB s2 p1)) (cap d1l cl)) of ViewCap d1l' c2 -> Cap (RY l2 (D2 d1l' d1r) s1) c2
      DOL ot -> case uncap (pushOnly (S3 rem2 (plugR d2 cr) (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RY l2 (DOL ot2) s1) c2
  where
    aux :: Buffer q i' j' -> HPair (Buffer q) i' j'
    aux p1 g = case popB p1 of
      H p1l1 srem1 -> case popB (shiftless srem1) of
        H p1l2 srem2 -> H (B2 p1l1 p1l2) (shiftless srem2)

    only :: Cap OnlyTriple q i j -> Cap RightTriple q i j
    only (Triple O0{}) = error "Impossible"
    only (Triple (OGG p1 D0 s1)) = onlyPS p1 s1
    only (Triple (ORX p1 D0 s1)) = onlyPS p1 s1
    only (Triple (OXR p1 D0 s1)) = onlyPS p1 s1
    only (Triple (OGG p1 d1 s1)) = case aux p1 of H l2 rem2 -> Triple $ RG l2 (push (S1 rem2) d1) s1
    only (Triple (ORX p1 d1 s1@B5{})) = case aux p1 of
      H l2 rem2 -> case d1 of
        D2 lt rt -> Triple (RR l2 (D2 (pushLeft (S1 rem2) lt) rt) s1)
        DOR ot -> Triple (RR l2 (DOR (pushOnly (S1 rem2) ot)) s1)
        DOL ot -> Triple (RR l2 (DOR (pushOnly (S1 rem2) ot)) s1)
        D0 -> Triple (RR l2 (DOR (Triple (O0 (B1 (S1 rem2))))) s1)
    only (Triple (ORX p1 d1 s1@B6{})) = case aux p1 of
      H l2 rem2 -> case d1 of
        D2 lt rt -> case uncap rt of ViewCap rt2 cap2 -> Cap (RO l2 (D2 (pushLeft (S1 rem2) lt) rt2) s1) cap2
        DOR ot -> case uncap (pushOnly (S1 rem2) ot) of ViewCap ot2 c2 -> Cap (RO l2 (DOR ot2) s1) c2
        DOL ot -> case uncap (pushOnly (S1 rem2) ot) of ViewCap ot2 c2 -> Cap (RO l2 (DOR ot2) s1) c2
        D0 -> Cap (RO l2 (DOR Opening) s1) (O0 (B1 (S1 rem2)))
    only (Triple (ORX p1 d1 s1@B7{})) = case aux p1 of
      H l2 rem2 -> case d1 of
        D2 lt rt -> case uncap (pushLeft (S1 rem2) lt) of ViewCap lt2 cap2 -> Cap (RY l2 (D2 lt2 rt) s1) cap2
        DOR ot -> case uncap (pushOnly (S1 rem2) ot) of ViewCap ot2 c2 -> Cap (RY l2 (DOL ot2) s1) c2
        DOL ot -> case uncap (pushOnly (S1 rem2) ot) of ViewCap ot2 c2 -> Cap (RY l2 (DOL ot2) s1) c2
        D0 -> Cap (RY l2 (DOL Opening) s1) (O0 (B1 (S1 rem2)))
    only (Triple (ORX p1 d1 s1@B8{})) = case aux p1 of
      H l2 rem2 -> case d1 of
        D2 lt rt -> Triple (RG l2 (D2 (pushLeft (S1 rem2) lt) rt) s1)
        DOR ot -> Triple (RG l2 (DOL (pushOnly (S1 rem2) ot)) s1)
        DOL ot -> Triple (RG l2 (DOL (pushOnly (S1 rem2) ot)) s1)
        D0 -> Triple (RG l2 (DOR (Triple (O0 (B1 (S1 rem2))))) s1)
    only (Triple (ORX p1 d1 s1@B9{})) = case aux p1 of
      H l2 rem2 -> case d1 of
        D2 lt rt -> Triple (RG l2 (D2 (pushLeft (S1 rem2) lt) rt) s1)
        DOR ot   -> Triple (RG l2 (DOL (pushOnly (S1 rem2) ot)) s1)
        DOL ot   -> Triple (RG l2 (DOL (pushOnly (S1 rem2) ot)) s1)
        D0 -> Triple (RG l2 (DOR (Triple (O0 (B1 (S1 rem2))))) s1)
    only (Cap (OOX p1 d1 s1@B6{}) c) = case aux p1 of
      H l2 rem2 -> case d1 of
        D2 lt rt -> Cap (RO l2 (D2 (pushLeft (S1 rem2) lt) rt) s1) c
        DOR ot   -> case uncap (pushOnly (S1 rem2) ot) of
          ViewCap ot2 c2 -> Cap (RO l2 (DOR ot2) s1) c2
    only (Cap (OOX p1 d1 s1@B7{}) c) = case aux p1 of
      H l2 rem2 -> case pushOnly (S1 rem2) (plugR d1 c) of
        D2 lt rt -> case uncap lt of ViewCap lt2 c2 -> Cap (RY l2 (D2 lt2 rt) s1) c2
        DOL ot -> case uncap ot of ViewCap ot2 c2 -> Cap (RY l2 (DOL ot2) s1) c2
        DOR ot -> case uncap ot of ViewCap ot2 c2 -> Cap (RY l2 (DOL ot2) s1) c2
        D0 -> error "Impossible"
    only (Cap (OOX p1 d1 s1@B8{}) c) = case aux p1 of
      H l2 rem2 -> Triple $ RG l2 (push (S1 rem2) (plugR d1 c)) s1
    only (Cap (OOX p1 d1 s1@B9{}) c) = case aux p1 of
      H l2 rem2 -> Triple $ RG l2 (push (S1 rem2) (plugR d1 c)) s1
    only (Cap (OXO p1 d1 s1) c) = case aux p1 of
      H l2 rem2 -> case d1 of
        D2 lt rt -> Cap (RO l2 (D2 (pushLeft (S1 rem2) lt) rt) s1) c
        DOR ot -> case uncap (pushOnly (S1 rem2) (cap ot c)) of ViewCap ot2 c2 -> Cap (RO l2 (DOR ot2) s1) c2
    only (Triple (OXR p1 d1 s1)) = case aux p1 of
      H l2 rem2 -> case d1 of
        D2 lt rt -> Triple $ RR l2 (D2 (pushLeft (S1 rem2) lt) rt) s1
        DOR ot -> Triple $ RR l2 (DOR (pushOnly (S1 rem2) ot)) s1
        DOL ot -> Triple $ RR l2 (DOR (pushOnly (S1 rem2) ot)) s1
        D0 -> Triple $ RR l2 (DOR (Triple (O0 (B1 (S1 rem2))))) s1
    only (Cap (OYX p1 d1 s1@B7{}) c) = case aux p1 of
      H l2 rem2 -> case plugL c d1 of
        D2 lt rt -> case uncap (pushLeft (S1 rem2) lt) of ViewCap lt2 c2 -> Cap (RY l2 (D2 lt2 rt) s1) c2
        DOL ot -> case uncap (pushOnly (S1 rem2) ot) of ViewCap ot2 c2 -> Cap (RY l2 (DOL ot2) s1) c2
        DOR _ -> error "Impossible"
        D0 -> error "Impossible"
    only (Cap (OYX p1 d1 s1@B8{}) c) = case aux p1 of
      H l2 rem2 -> Triple (RG l2 (push (S1 rem2) (plugL c d1)) s1)
    only (Cap (OYX p1 d1 s1@B9{}) c) = case aux p1 of
      H l2 rem2 -> Triple (RG l2 (push (S1 rem2) (plugL c d1)) s1)
    only (Cap (OGY p1 d1 s1) c) = case aux p1 of
      H l2 rem2 -> case plugL c d1 of
        D2 lt rt -> case uncap (pushLeft (S1 rem2) lt) of ViewCap lt2 c2 -> Cap (RY l2 (D2 lt2 rt) s1) c2
        DOL ot -> case uncap (pushOnly (S1 rem2) ot) of ViewCap ot2 c2 -> Cap (RY l2 (DOL ot2) s1) c2
        DOR _ -> error "Impossible"
        D0 -> error "Impossible"

    onlyPS :: Buffer q j' j -> Buffer q i j' -> Cap RightTriple q i j
    onlyPS p1@B9{} s1 = case ejectB p1 of
        H srem1 p1r1 -> case ejectB (shiftless srem1) of
          H srem2 p1r2 -> case ejectB (shiftless srem2) of
            H srem3 p1r3 -> case aux (shiftless srem3) of
              H p2 rem5 -> Triple $ RG p2 (push (S1 rem5) D0) $ pushB p1r3 (pushB p1r2 (pushB p1r1 s1))

    onlyPS p1 s1 = case aux p1 of
      H l2 rem2 -> Triple $ RG l2 D0 (catenateB rem2 s1)

data View l r a c where
  Empty :: View l r a a
  (:|) :: l b c -> r a b -> View l r a c

data View3 q a c where
  V0 :: View3 q a a
  V1 :: q a c -> View3 q a c
  V3 :: q c d -> Deque q b c -> q a b -> View3 q a d

popNoRepair :: Deque q i j -> View q (Deque q) i j
popNoRepair d = case d of
  D0 -> Empty
  D2 lt rt -> case popLeftNoRepair lt of
    Left (H a b) -> (a :|) . DOL $ case rt of
      Triple (R0 p1 s1) -> Triple $ O0 (catenateB b (catenateB p1 s1))
      Triple (RG p1 d1 s1) -> Triple $ OGG (catenateB b p1) d1 s1
      Cap (RO p1 d1 s1) cap1 -> Cap (OXO (catenateB b p1) d1 s1) cap1
      Cap (RY p1 d1 s1) cap1 -> Cap (OGY (catenateB b p1) d1 s1) cap1
    Right (H a lt') -> a :| D2 lt' rt
  DOL ot -> popOnlyNoRepair ot
  DOR ot -> popOnlyNoRepair ot

popLeftNoRepair :: Cap LeftTriple q j k -> Either (HPair q (Buffer q) j k) (HPair q (Cap LeftTriple q) j k)
popLeftNoRepair c = case c of
  Triple (LG p1 d1 s1) -> case popB p1 of
    H p1l1 (Shift rem1@B7{}) -> case d1 of
      D2 lt2 rt2 -> case uncap lt2 of ViewCap lt3 cap3 -> Right $ p1l1 `H` Cap (LY rem1 (D2 lt3 rt2) s1) cap3
      DOL ot -> case uncap ot of ViewCap ot2 cap2 -> Right $ p1l1 `H` Cap (LY rem1 (DOL ot2) s1) cap2
      DOR ot -> case uncap ot of ViewCap ot2 cap2 -> Right $ p1l1 `H` Cap (LY rem1 (DOL ot2) s1) cap2
      D0 -> Right $ p1l1 `H` Triple (L0 rem1 s1)
    H p1l1 srem1 -> Right $ p1l1 `H` Triple (LG (shiftless srem1) d1 s1)
  Cap (LY p1 d1 s1) cap1 -> case popB p1 of
    H p1l1 (Shift rem1) -> case d1 of
      D2 lt2 rt2 -> case uncap rt2 of ViewCap rt3 cap3 -> Right $ p1l1 `H` Cap (LO rem1 (D2 (cap lt2 cap1) rt3) s1) cap3
      DOL ot -> Right $ p1l1 `H` Cap (LO rem1 (DOR ot) s1) cap1
  Cap (LO p1 d1 s1) cap1 -> case popB p1 of
    H p1l1 (Shift rem1) -> case d1 of
      D2 lt2 rt2 -> Right $ p1l1 `H` Triple (LR rem1 (D2 lt2 (cap rt2 cap1)) s1)
      DOR ot -> Right $ p1l1 `H` Triple (LR rem1 (DOR (cap ot cap1)) s1)
  Triple (L0 p1 s1) -> case popB p1 of
    H p1l1 (Shift rem1@B4{}) -> Left $ p1l1 `H` catenateB rem1 s1
    H p1l1 srem1 -> Right $ p1l1 `H` Triple (L0 (shiftless srem1) s1)

ejectRightNoRepair :: Cap RightTriple q i j -> Either (HPair (Buffer q) q i j) (HPair (Cap RightTriple q) q i j)
ejectRightNoRepair c = case c of
  Triple (RG p1 d1 s1) -> case ejectB s1 of
    H (Shift rem1@B7{}) s1r1 -> case d1 of
      D2 lt2 rt2 -> case uncap lt2 of ViewCap lt3 cap3 -> Right $ Cap (RY p1 (D2 lt3 rt2) rem1) cap3 `H` s1r1
      DOL ot -> case uncap ot of ViewCap ot2 cap2 -> Right $ Cap (RY p1 (DOL ot2) rem1) cap2 `H` s1r1
      DOR ot -> case uncap ot of ViewCap ot2 cap2 -> Right $ Cap (RY p1 (DOL ot2) rem1) cap2 `H` s1r1
      D0 -> Right $  Triple (R0 p1 rem1) `H` s1r1
    H srem1 s1r1 -> Right $ Triple (RG p1 d1 (shiftless srem1)) `H` s1r1
  Cap (RY p1 d1 s1) cap1 -> case ejectB s1 of
    H (Shift rem1) s1r1 -> case d1 of
      D2 lt2 rt2 -> case uncap rt2 of ViewCap rt3 cap3 -> Right $ Cap (RO p1 (D2 (cap lt2 cap1) rt3) rem1) cap3 `H` s1r1
      DOL ot -> Right $ Cap (RO p1 (DOR ot) rem1) cap1 `H` s1r1
  Cap (RO p1 d1 s1) cap1 -> case ejectB s1 of
    H (Shift rem1) s1r1 -> case d1 of
      D2 lt2 rt2 -> Right $ Triple (RR p1 (D2 lt2 (cap rt2 cap1)) rem1) `H` s1r1
      DOR ot -> Right $ Triple (RR p1 (DOR (cap ot cap1)) rem1) `H` s1r1
  Triple (R0 p1 s1) -> case ejectB s1 of
    H (Shift rem1@B4{}) s1r1 -> Left $ catenateB p1 rem1 `H` s1r1
    H srem1 s1r1 -> Right $ Triple (R0 p1 (shiftless srem1)) `H` s1r1

popOnlyNoRepair :: Cap OnlyTriple q i j -> View q (Deque q) i j
popOnlyNoRepair (Triple (O0 p1)) = case popB p1 of
      H p1l1 NoB -> p1l1 :| D0
      H p1l1 srem1 -> p1l1 :| DOL (Triple (O0 (shiftless srem1)))
popOnlyNoRepair (Triple (OGG p1 d1 s1)) = case popB p1 of
      H p1l1 (Shift rem1@B7{}) -> case d1 of
        D2 lt2 rt2 -> case uncap lt2 of ViewCap lt3 cap3 -> p1l1 :| DOL (Cap (OYX rem1 (D2 lt3 rt2) s1) cap3)
        DOL ot -> case uncap ot of ViewCap ot3 cap3 -> p1l1 :| DOL (Cap (OYX rem1 (DOL ot3) s1) cap3)
        DOR ot -> case uncap ot of ViewCap ot3 cap3 -> p1l1 :| DOL (Cap (OYX rem1 (DOL ot3) s1) cap3)
        D0 -> p1l1 :| DOL (Triple (O0 (catenateB rem1 s1)))
      H p1l1 srem1 -> p1l1 :| DOL (Triple (OGG (shiftless srem1) d1 s1))
popOnlyNoRepair (Cap (OOX p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> p1l1 :| DOL (Triple (ORX rem1 (plugR d1 cap1) s1))
popOnlyNoRepair (Cap (OXO p1 d1 s1) cap1) = case popB p1 of
      H p1l1 srem1 -> p1l1 :| DOL (Cap (OOX (shiftless srem1) d1 s1) cap1)
popOnlyNoRepair (Cap (OYX p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> case d1 of
        D2 lt2 rt2 -> case uncap rt2 of ViewCap rt3 cap3 -> p1l1 :| DOL (Cap (OOX rem1 (D2 (cap lt2 cap1) rt3) s1) cap3)
        DOL ot -> p1l1 :| DOL (Cap (OOX rem1 (DOR ot) s1) cap1)
popOnlyNoRepair (Cap (OGY p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1@B7{}) -> p1l1 :| DOL (Cap (OYX rem1 d1 s1) cap1)
      H p1l1 srem1 -> p1l1 :| DOL (Cap (OGY (shiftless srem1) d1 s1) cap1)

popEjectOnlyNoRepair :: Cap OnlyTriple q i j -> View3 q i j
popEjectOnlyNoRepair (Triple (O0 p1)) = case popB p1 of
      H p1l1 NoB -> V1 p1l1
      H p1l1 srem1 -> case ejectB (shiftless srem1) of
        H srem2 p1r1 -> V3 p1l1 (DOL (Triple (O0 (shiftless srem2)))) p1r1
popEjectOnlyNoRepair (Triple (OGG p1 d1 s1)) = case popB p1 of
      H p1l1 (Shift rem1@B7{}) -> case ejectB s1 of
        H (shiftless -> rem2) s1r1 -> case d1 of
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
        H srem2 s1r1 -> V3 p1l1 (DOL (Triple (OGG rem1 d1 (shiftless srem2)))) s1r1
      H p1l1 (NoShift rem1) -> case ejectB s1 of
        H (Shift rem2@B7{}) s1r1 -> case d1 of
          D2 lt2 rt2 -> case uncap lt2 of ViewCap lt3 cap3 -> V3 p1l1 (DOL (Cap (OGY rem1 (D2 lt3 rt2) rem2) cap3)) s1r1
          DOL ot -> case uncap ot of ViewCap ot3 cap3 -> V3 p1l1 (DOL (Cap (OGY rem1 (DOL ot3) rem2) cap3)) s1r1
          DOR ot -> case uncap ot of ViewCap ot3 cap3 -> V3 p1l1 (DOL (Cap (OGY rem1 (DOL ot3) rem2) cap3)) s1r1
          D0 -> V3 p1l1 (DOL (Triple (O0 (catenateB rem1 rem2)))) s1r1
        H srem2 s1r1 -> V3 p1l1 (DOL (Triple (OGG rem1 d1 (shiftless srem2)))) s1r1
popEjectOnlyNoRepair (Cap (OOX p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> case ejectB s1 of
        H srem2 s1r1 -> V3 p1l1 (DOL (Triple (ORX rem1 (plugR d1 cap1) (shiftless srem2)))) s1r1
popEjectOnlyNoRepair (Cap (OXO p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (shiftless -> rem1) -> case ejectB s1 of
        H (Shift rem2) s1r1 -> V3 p1l1 (DOL (Triple (OXR rem1 (plugR d1 cap1) rem2))) s1r1
popEjectOnlyNoRepair (Cap (OYX p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> case ejectB s1 of
        H (shiftless -> rem2) s1r1 -> case d1 of
          D2 lt2 rt2 -> case uncap rt2 of ViewCap rt3 cap3 -> V3 p1l1 (DOL (Cap (OOX rem1 (D2 (cap lt2 cap1) rt3) rem2) cap3)) s1r1
          DOL ot -> V3 p1l1 (DOL (Cap (OOX rem1 (DOR ot) rem2) cap1)) s1r1
popEjectOnlyNoRepair (Cap (OGY p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (shiftless -> rem1) -> case ejectB s1 of
        H (Shift rem2) s1r1 -> case d1 of
          D2 lt2 rt2 -> case uncap rt2 of ViewCap rt3 cap3 -> V3 p1l1 (DOL (Cap (OXO rem1 (D2 (cap lt2 cap1) rt3) rem2) cap3)) s1r1
          DOL ot -> V3 p1l1 (DOL (Cap (OXO rem1 (DOR ot) rem2) cap1)) s1r1

ejectOnlyNoRepair :: Cap OnlyTriple q i j -> View (Deque q) q i j
ejectOnlyNoRepair c = case popEjectOnlyNoRepair c of
  V0 -> Empty
  V1 a -> D0 :| a
  V3 a b c -> push a b :| c

ejectNoRepair :: Deque q i j -> View (Deque q) q i j
ejectNoRepair d = case d of
  D0 -> Empty
  D2 lt rt -> case ejectRightNoRepair rt of
    Left (b `H` r) -> ( :| r) . DOL $ case lt of
      Triple (L0 p1 s1) -> Triple (O0 (catenateB (catenateB p1 s1) b))
      Triple (LG p1 d1 s1) -> Triple (OGG p1 d1 (catenateB s1 b))
      Cap (LO p1 d1 s1) cap1 -> Cap (OOX p1 d1 (catenateB s1 b)) cap1
      Cap (LY p1 d1 s1) cap1 -> Cap (OYX p1 d1 (catenateB s1 b)) cap1
    Right (rt' `H` r) -> D2 lt rt' :| r
  DOL ot -> ejectOnlyNoRepair ot
  DOR ot -> ejectOnlyNoRepair ot

popEjectNoRepair :: Deque q i j -> View3 q i j
popEjectNoRepair D0 = V0
popEjectNoRepair (DOL ot) = popEjectOnlyNoRepair ot
popEjectNoRepair (DOR ot) = popEjectOnlyNoRepair ot
popEjectNoRepair (D2 lt rt) = case ejectRightNoRepair rt of
  Left (H rb r1) -> case popLeftNoRepair lt of
    Left (H l1 lb) -> V3 l1 (DOL (Triple (O0 (catenateB lb rb)))) r1
    Right (H l1 lt') -> case lt' of
      Triple (LG p2 d2 s2) -> V3 l1 (DOL (Triple (OGG p2 d2 (catenateB s2 rb)))) r1
      Triple (LR p2 d2 s2) -> V3 l1 (DOL (Triple (ORX p2 d2 (catenateB s2 rb)))) r1
      Triple (L0 p2 s2) -> V3 l1 (DOL (Triple (O0 (catenateB (catenateB p2 s2) rb)))) r1
      Cap (LO p2 d2 s2) cap1 -> V3 l1 (DOL (Cap (OOX p2 d2 (catenateB s2 rb)) cap1)) r1
      Cap (LY p2 d2 s2) cap1 -> V3 l1 (DOL (Cap (OYX p2 d2 (catenateB s2 rb)) cap1)) r1
  Right (H rt' r1) -> case popLeftNoRepair lt of
    Left (H l1 lb) -> case rt' of
      Triple (RG p2 d2 s2) -> V3 l1 (DOL (Triple (OGG (catenateB lb p2) d2 s2))) r1
      Triple (RR p2 d2 s2) -> V3 l1 (DOL (Triple (OXR (catenateB lb p2) d2 s2))) r1
      Triple (R0 p2 s2) -> V3 l1 (DOL (Triple (O0 (catenateB lb (catenateB p2 s2))))) r1
      Cap (RO p2 d2 s2) cap1 -> V3 l1 (DOL (Cap (OXO (catenateB lb p2) d2 s2) cap1)) r1
      Cap (RY p2 d2 s2) cap1 -> V3 l1 (DOL (Cap (OGY (catenateB lb p2) d2 s2) cap1)) r1
    Right (H l1 lt') -> V3 l1 (D2 lt' rt') r1
    
   
popThenPush :: forall lg lr q i k foo m. (Monad m) => Deque q i k -> (forall j. q j k -> m (HPair foo q j k)) -> m (View foo (Deque q) i k)
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
    only :: Cap OnlyTriple q i' k -> m (HPair foo (Cap OnlyTriple q) i' k)
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

repairLeftTriple :: LeftTriple q i j -> LeftTriple q i j
repairLeftTriple l = case l of
  LR p1 d1 s1 -> case popNoRepair d1 of
    S3 p2 d2 s2 :| d1' -> LG (catenateB p1 p2) (catenate' d2 (push (S1 s2) d1')) s1
    S1 p2 :| d1' -> LG (catenateB p1 p2) d1' s1
    Empty -> L0 p1 s1
  L0{} -> l
  LG{} -> l

repairCap :: Repairable r => Cap r q i j -> Cap r q i j
repairCap (Triple c) = Triple (repair c)
repairCap (Cap o c) = Cap o (repair c)

repairRightTriple :: RightTriple q i j -> RightTriple q i j
repairRightTriple r = case r of
  RR p1 d1 s1 -> case ejectNoRepair d1 of
    d1' :| S3 p2 d2 s2 -> RG p1 (catenate' (inject d1' (S1 p2)) d2) (catenateB s2 s1)
    d1' :| S1 p2 -> RG p1 d1' (catenateB p2 s1)
    Empty -> R0 p1 s1
  R0{} -> r
  RG{} -> r

repairOnlyTriple :: OnlyTriple q i j -> OnlyTriple q i j
repairOnlyTriple o = case o of
  ORX p1 d1 s1@B8{} -> case popNoRepair d1 of
    S3 p2 d2 s2 :| d1' -> OGG (catenateB p1 p2) (catenate' d2 (push (S1 s2) d1')) s1
    S1 p2 :| d1' -> OGG (catenateB p1 p2) d1' s1
    Empty -> O0 (catenateB p1 s1)
  ORX p1 d1 s1@B9{} -> case popNoRepair d1 of
    S3 p2 d2 s2 :| d1' -> OGG (catenateB p1 p2) (catenate' d2 (push (S1 s2) d1')) s1
    S1 p2 :| d1' -> OGG (catenateB p1 p2) d1' s1
    Empty -> O0 (catenateB p1 s1)
  OXR p1@B8{} d1 s1 -> case ejectNoRepair d1 of
    d1' :| S3 p2 d2 s2 -> OGG p1 (catenate' (inject d1' (S1 p2)) d2) (catenateB s2 s1)
    d1' :| S1 p2 -> OGG p1 d1' (catenateB p2 s1)
    Empty -> O0 (catenateB p1 s1)
  OXR p1@B9{} d1 s1 -> case ejectNoRepair d1 of
    d1' :| S3 p2 d2 s2 -> OGG p1 (catenate' (inject d1' (S1 p2)) d2) (catenateB s2 s1)
    d1' :| S1 p2 -> OGG p1 d1' (catenateB p2 s1)
    Empty -> O0 (catenateB p1 s1)
  ORX p1 d1 s1 -> go p1 d1 s1
  OXR p1 d1 s1 -> go p1 d1 s1
  OGG{} -> o
  O0{} -> o
  where
    go :: Buffer q k l -> Deque (StoredTriple q) j k -> Buffer q i j -> OnlyTriple q i l
    go p1 d1 s1 = case popEjectNoRepair d1 of
      V0 -> O0 (catenateB p1 s1)
      V1 (S1 p2) -> O0 (catenateB (catenateB p1 p2) s1)
      V1 (S3 p2 d2 s2) -> OGG (catenateB p1 p2) d2 (catenateB s2 s1)
      V3 (S1 p2) d1'' (S1 p3) -> OGG (catenateB p1 p2) d1'' (catenateB p3 s1)
      V3 (S3 p2 d2 s2) d1'' (S1 p3) -> OGG (catenateB p1 p2) (catenate' d2 (push (S1 s2) d1'')) (catenateB p3 s1)
      V3 (S1 p2) d1'' (S3 p3 d3 s3) -> OGG (catenateB p1 p2) (catenate' (inject d1'' (S1 p3)) d3) (catenateB s3 s1)
      V3 (S3 p2 d2 s2) d1' (S3 p3 d3 s3) -> OGG (catenateB p1 p2) (catenate' (catenate' d2 (inject (push (S1 s2) d1') (S1 p3))) d3) (catenateB s3 s1)

instance Repairable LeftTriple where repair = repairLeftTriple

instance Repairable OnlyTriple where repair = repairOnlyTriple

instance Repairable RightTriple where repair = repairRightTriple

pop :: Deque q i j -> View q (Deque q) i j
pop d = case popNoRepair d of
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

mkDeq :: Int -> Int -> Deque Foo () ()
mkDeq m n = foldr (\a d -> catenate d $ iterate (push (F a)) empty !! m) empty [1..n]

sumDeq :: Deque Foo () () -> Int
sumDeq = sum . unfoldr go
  where
    go :: Deque Foo () () -> Maybe (Int, Deque Foo () ())
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
