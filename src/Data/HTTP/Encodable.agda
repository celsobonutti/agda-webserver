module Data.HTTP.Encodable where

open import Prelude
open List using (intercalate)
open String using (_++_; intersperse)

record HttpEncodable {a} (A : Set a) : Set a where
  field
    encode : A → String
    decode : String → Maybe A

open HttpEncodable ⦃...⦄ public

instance
  maybeEncodable : ∀ {a} {A : Set a} → ⦃ HttpEncodable A ⦄ → HttpEncodable (Maybe A)
  maybeEncodable {A = A} = record
    { encode = λ { nothing → "null"; (just x) → encode x }
    ; decode = λ { "null" → just nothing; x → just (decode x) }
    }

  listEncodable : ∀ {a} {A : Set a} → ⦃ HttpEncodable A ⦄ → HttpEncodable (List A)
  listEncodable {A = A} ⦃ httpEncodable ⦄ = record
    { encode = λ xs → "[" ++ (intersperse "," (List.map encode xs)) ++ "]"
    ; decode = λ x → nothing
    }
