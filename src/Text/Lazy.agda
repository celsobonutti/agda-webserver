module Text.Lazy where

open import Data.String renaming (String to Text)
open import Agda.Builtin.FromString
open import Data.Unit
open import Data.Nat

{-# FOREIGN GHC

import Data.Text.Lazy as TL

#-}

postulate
  Lazy : Set
  toStrict : Lazy -> Text
  fromStrict : Text -> Lazy

{-# COMPILE GHC Lazy = type TL.Text #-}
{-# COMPILE GHC toStrict = TL.toStrict #-}
{-# COMPILE GHC fromStrict = TL.fromStrict #-}

instance
  LazyString : IsString Lazy
  LazyString = record { Constraint = λ _ → ⊤
                      ; fromString = λ s → fromStrict s
                      }

_ : Lazy
_ = "/get"
