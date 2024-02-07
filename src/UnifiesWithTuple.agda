module UnifiesWithTuple where

open import Prelude
open import Level using (0ℓ)
open import Level.Literals using (#_)
open import Relation.Binary using (Rel; REL)
open import Data.Product using (_×_)
open import Relation.Unary using (Decidable; Pred)
open import Data.Nat
open import Relation.Nullary.Decidable
import Data.Nat.Show as Nat
open import Function.Base using (case_of_)
open import Data.HTTP.Encodable
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality hiding ([_])

data UnifiesWithTuple : REL Set ℕ (# 1) where
  tup : ∀ {n : ℕ} {t₁ t₂ : Set} ⦃ http : HttpEncodable t₁ ⦄ → UnifiesWithTuple t₂ n → UnifiesWithTuple (t₁ × t₂) (suc n)
  base : ∀ {t : Set} ⦃ http : HttpEncodable t ⦄ → UnifiesWithTuple t 1

data VarType : Set where
  listV : VarType
  optional : VarType
  common : VarType

data UnifiesWithTupleV : REL Set (List VarType) (# 1) where
  tupL : ∀ {n} {t₁ t₂ : Set} ⦃ http : HttpEncodable t₁ ⦄
    → UnifiesWithTupleV t₂ n → UnifiesWithTupleV (List t₁ × t₂) (listV ∷ n)
  tupO : ∀ {n} {t₁ t₂ : Set} ⦃ http : HttpEncodable t₁ ⦄
    → UnifiesWithTupleV t₂ n → UnifiesWithTupleV (Maybe t₁ × t₂) (optional ∷ n)
  tupC : ∀ {n} {t₁ t₂ : Set}  ⦃ http : HttpEncodable t₁ ⦄
    → UnifiesWithTupleV t₂ n → UnifiesWithTupleV (t₁ × t₂) (common ∷ n)
  baseL : ∀ {t : Set} ⦃ http : HttpEncodable t ⦄ → UnifiesWithTupleV (List t) [ listV ]
  baseO : ∀ {t : Set} ⦃ http : HttpEncodable t ⦄ → UnifiesWithTupleV (Maybe t) [ optional ]
  baseC : ∀ {t : Set} ⦃ http : HttpEncodable t ⦄ → UnifiesWithTupleV t [ common ]

instance
    find-base : {t : Set} → ⦃ HttpEncodable t ⦄ → UnifiesWithTuple t 1
    find-base ⦃ http ⦄ = base

    find-tup : {n : ℕ} {t₁ t₂ : Set} → ⦃ HttpEncodable t₁ ⦄ → ⦃ UnifiesWithTuple t₂ n ⦄ → UnifiesWithTuple (t₁ × t₂) (suc n)
    find-tup {n} {t₁} {t₂} ⦃ http ⦄ ⦃ x ⦄ = tup x

    find-tupL : {n : List VarType} {t₁ t₂ : Set} → ⦃ HttpEncodable t₁ ⦄ → ⦃ UnifiesWithTupleV t₂ n ⦄ → UnifiesWithTupleV (List t₁ × t₂) (listV ∷ n)
    find-tupL {n} {t₁} {t₂} ⦃ http ⦄ ⦃ x ⦄ = tupL x

    find-tupO : {n : List VarType} {t₁ t₂ : Set} → ⦃ HttpEncodable t₁ ⦄ →  ⦃ UnifiesWithTupleV t₂ n ⦄ → UnifiesWithTupleV (Maybe t₁ × t₂) (optional ∷ n)
    find-tupO {n} {t₁} {t₂} ⦃ http ⦄ ⦃ x ⦄ = tupO x

    find-tupC : {n : List VarType} {t₁ t₂ : Set} → ⦃ HttpEncodable t₁ ⦄ →  ⦃ UnifiesWithTupleV t₂ n ⦄ → UnifiesWithTupleV (t₁ × t₂) (common ∷ n)
    find-tupC {n} {t₁} {t₂} ⦃ http ⦄ ⦃ x ⦄ = tupC x

    find-baseL : {t : Set} → ⦃ HttpEncodable t ⦄ → UnifiesWithTupleV (List t) [ listV ]
    find-baseL ⦃ http ⦄ = baseL

    find-baseO : {t : Set} → ⦃ HttpEncodable t ⦄ → UnifiesWithTupleV (Maybe t) [ optional ]
    find-baseO ⦃ http ⦄ = baseO

    find-baseC : {t : Set} → ⦃ HttpEncodable t ⦄ → UnifiesWithTupleV t [ common ]
    find-baseC ⦃ http ⦄ = baseC

constrain : {n : ℕ} → (x : Set) → {{UnifiesWithTuple x n}} → Set
constrain = λ x → x

constrainV : ∀ {n} → (x : Set) → {{UnifiesWithTupleV x n}} → Set
constrainV = λ x → x

instance
  natEncodable : HttpEncodable ℕ
  natEncodable = record { encode = λ n → Nat.show n
                        ; decode = λ s → Nat.readMaybe 10 s
                        }

instance
  stringEncodable : HttpEncodable String
  stringEncodable = record { encode = id ; decode = just }

instance
  charEncodable : HttpEncodable Char
  charEncodable = record { encode = λ a → String.fromList ([ a ])
                         ; decode = λ s → case String.toList s of λ
                           { (a ∷ []) → just a
                           ; _     → nothing
                           }
                         }


_ : Set
_ = constrainV {optional ∷ listV ∷ common ∷ []} (Maybe ℕ × List ℕ × ℕ)

_ : Set
_ = constrain {5} (ℕ × ℕ × ℕ × ℕ × ℕ)

_ : Set
_ = constrain {2} (ℕ × ℕ)
