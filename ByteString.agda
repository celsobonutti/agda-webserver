module ByteString where

open import Agda.Builtin.FromString
open import Data.String using (String)
open import Data.Unit

{-# FOREIGN GHC

import Data.Text (pack, unpack)

#-}

postulate
  Text : Set
  pack : String → Text
  unpack : Text → String

{-# COMPILE GHC pack = pack #-}
{-# COMPILE GHC unpack = unpack #-}

