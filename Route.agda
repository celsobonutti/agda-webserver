{-# OPTIONS --guardedness #-}
module Route where

import Agda.Builtin.Unit as Prim
open import Data.Nat using (ℕ; suc)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; _++_; [_])
open import Scotty using (countParams; captureParams; ScottyM)
open import Data.Bool using (T?; true; Bool; false)
open import Data.Vec using (Vec; _∷_; [])
import Data.List as List
import Data.Vec as Vec
import Scotty
open import Function.Base using (_∘_)
import Foreign.Haskell.Pair as Pair
import Text.Lazy as Text

record HttpEncodable {a} (A : Set a) : Set a where
  field
    encode : A → String
    decode : String → Maybe A

open HttpEncodable {{...}} public

data Appliable : ℕ → Set₁ where
  Mk : Appliable 0
  Apply : {n : ℕ} → (X : Set) → {{HttpEncodable X}} → Appliable n → Appliable (suc n)

⟨_⟩ : (X : Set) → {{HttpEncodable X}} → Appliable 1
⟨ x ⟩ = Apply x Mk

_⟫ : (X : Set) → {{HttpEncodable X}} → Appliable 1
_⟫ x = Apply x Mk

⟪_ : (X : Set) → Set
⟪ x = x

_×_ : ∀ {n : ℕ} → (X : Set) → Appliable n → {{HttpEncodable X}} → Appliable (suc n)
x × ap = Apply x ap

infix 10 ⟪_
infix 20 _⟫
infixr 5 _×_

toFunction : {n : ℕ} → Appliable n → Set → Set
toFunction Mk ret = ret
toFunction (Apply T applies) ret = T → toFunction applies ret

data Route : Set₁ where
  Get : (route : String) → (arguments : Appliable (countParams route)) → (returnType : Set) → {{HttpEncodable returnType}} → toFunction arguments returnType → Route
  -- Post : (route : String) → (arguments : Appliable (countParams route)) → (body : Set) → (returnType : Set) → toFunction arguments (body → returnType) → Route

apply : ∀ {n : ℕ} → {A : Set} → (arguments : Appliable n) → Vec Scotty.Param n → toFunction arguments A → Maybe A
apply Mk _ f = just f
apply (Apply X {{i}} x) ( param ∷ tail) f = do
  decoded ← decode (Text.toStrict (Pair.snd param))
  apply x tail (f decoded)
  where open Data.Maybe

apply' : ∀ {n : ℕ} → {A : Set} → (arguments : Appliable n) → Vec String n → toFunction arguments A → Scotty.ActionM A
apply' Mk _ f = Scotty.ActionM.pure f
apply' {_} {A} (Apply X {{i}} x) (param ∷ tail) f = do
  param ← Scotty.captureParam (Text.fromStrict param)
  respond (decode param)
  where
    open Scotty.ActionM
    respond : Maybe X → Scotty.ActionM A
    respond (just value) = apply' x tail (f value)
    respond nothing = Scotty.raise (Text.fromStrict "Failed parsing parameter")


toScottyRoute : Route → ScottyM Prim.⊤
toScottyRoute (Get route arguments returnType {{i}} handler) =
  Scotty.get (Scotty.Capture (Text.fromStrict route)) handle
  where
    handle : Scotty.ActionM Prim.⊤
    handle = do
      let params = Scotty.getParams route
      response ← apply' arguments params handler
      Scotty.text (encode response)
      where
        open Scotty.ActionM

end : List Route
end = List.[]

_>>_ : Route → List Route → List Route
x >> y = x List.∷ y
