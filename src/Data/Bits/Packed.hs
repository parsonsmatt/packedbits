{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}

module Data.Bits.Packed where

import Data.Proxy
import GHC.Word
import GHC.TypeLits
import GHC.TypeLits.Extra
import Data.Word
import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Unboxed.Mutable as MV
import Data.Bits

-- | In Haskell, all of the 'Word8', 'Word16', etc. types are represented
-- internally as a pointer to a machine word. This can be memory
-- inefficient.
--
-- The 'Packed' type presents a separate interface: it packs together @n@
-- values of type @a@ provided that @a@ is an instance of 'Bits'.
newtype Packed n a = UnsafeMkPacked { unPacked :: Vector Word64 }
    deriving (Eq, Show)

type family PerWord64 a :: Nat

type instance PerWord64 Bool = 64
type instance PerWord64 Word8 = 8
type instance PerWord64 Word16 = 4
type instance PerWord64 Word32 = 2
type instance PerWord64 Word64 = 1

type family BitsIn a :: Nat

type instance BitsIn Bool = 1
type instance BitsIn Word8 = 8
type instance BitsIn Word16 = 16
type instance BitsIn Word32 = 32
type instance BitsIn Word64 = 64

-- | Produce a bitpacked structure of @n@ elements containing all 0s.
emptyP
    :: forall proxy bitSize n a mod div
    . ( KnownNat n
      , KnownNat bitSize
      , KnownNat mod
      , KnownNat div
      , bitSize ~ PerWord64 a
      , '(div, mod) ~ DivMod n bitSize
      )
    => proxy n 
    -> Packed n a
emptyP _ = UnsafeMkPacked $ 
    let count = fromInteger $ natVal (Proxy :: Proxy div) +
            case natVal (Proxy :: Proxy mod) of
                0 -> 0
                _ -> 1
     in V.replicate count 0
{-# INLINE empty #-}

empty
    :: forall n proxy bitSize a mod div
    . ( KnownNat n
      , KnownNat bitSize
      , Integral a
      , FiniteBits a
      , KnownNat mod
      , KnownNat div
      , bitSize ~ PerWord64 a
      , '(div, mod) ~ DivMod n bitSize
      )
    => Packed n a
empty = emptyP (Proxy :: Proxy n)

getP
    :: forall n m a proxy bitSize div mod
    . ( KnownNat n
      , KnownNat m
      , KnownNat bitSize
      , Integral a
      , FiniteBits a
      , CmpNat n m ~ LT
      , bitSize ~ BitsIn a
      , '(div, mod) ~ DivMod n bitSize
      )
    => proxy n
    -> Packed m a
    -> a
getP prxy (UnsafeMkPacked vec) =
    let 
        -- first, we need to get the index of the chunk that we care about
        -- this should be equal to the bitSize divided by the n
        bitSize = 
            natVal (Proxy :: Proxy bitSize)
        (indexChunk, indexSlot) = 
            (bitSize * natVal prxy) `divMod` 64
        -- then, we extract the word at that index
        word = 
            vec V.! fromInteger indexChunk
        adjusted =
            word `shiftR` fromIntegral indexSlot
     in fromIntegral adjusted

-- | Get the value at the given index out of the bitpacked vector.
get
    :: forall n m a proxy bitSize div mod
    . ( KnownNat n
      , KnownNat m
      , KnownNat bitSize
      , Integral a
      , FiniteBits a
      , CmpNat n m ~ LT
      , bitSize ~ BitsIn a
      , '(div, mod) ~ DivMod n bitSize
      )
    => Packed m a
    -> a
get = getP (Proxy :: Proxy n)

setP
    :: forall n m a proxy bitSize div mod
    . ( KnownNat n
      , KnownNat m
      , KnownNat bitSize
      , Integral a
      , FiniteBits a
      , CmpNat n m ~ LT
      , bitSize ~ BitsIn a
      , '(div, mod) ~ DivMod n bitSize
      )
    => proxy n
    -> a
    -> Packed m a
    -> Packed m a
setP prxy a (UnsafeMkPacked vec) = 
    let 
        -- first, we need to get the index of the chunk that we care about
        -- this should be equal to the bitSize divided by the n
        bitSize = 
            natVal (Proxy :: Proxy bitSize)
        (indexChunk, indexSlot) = 
            (bitSize * natVal prxy) `divMod` 64
        -- then, we extract the word at that index
        word = 
            vec V.! fromInteger indexChunk
        aWord = 
            fromIntegral a :: Word64
        mask = 
            aWord `shiftL` fromInteger indexSlot
        adjusted =
            (word .&. complement mask) .|. mask
     in UnsafeMkPacked $ V.modify (\mvec -> 
            MV.write mvec (fromIntegral indexChunk) adjusted) vec

set
    :: forall n m a proxy bitSize div mod
    . ( KnownNat n
      , KnownNat m
      , KnownNat bitSize
      , Integral a
      , FiniteBits a
      , CmpNat n m ~ LT
      , bitSize ~ BitsIn a
      , '(div, mod) ~ DivMod n bitSize
      )
    => a
    -> Packed m a
    -> Packed m a
set = setP (Proxy :: Proxy n)

example :: Packed 8 Word16
example = emptyP (Proxy :: Proxy 8)

