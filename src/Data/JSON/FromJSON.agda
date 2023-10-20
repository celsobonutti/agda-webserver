module Data.JSON.FromJSON where

open import Data.JSON
open import Prelude

record FromJSON {a} (A : Set a) : Set a where
  field
    fromJSON : JSON → Maybe A

record ToJSON {a} (A : Set a) : Set a where
  field
    toJSON : A → JSON

instance
  stringToJSON : ToJSON String
  stringToJSON = record { toJSON = λ x → JSON.string x }

instance
  natToJSON : ToJSON ℕ
  natToJSON = record { toJSON = λ x → JSON.number (Float.fromℕ x) }

instance
  natFromJSON : FromJSON ℕ
  natFromJSON = record { fromJSON = λ
                         { (JSON.number x) → toNat (Float.round x)
                         ; _ → nothing
                         }
                       }
