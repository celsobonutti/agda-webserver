module Route where

import Agda.Builtin.Unit as Prim
open import Data.Nat using (ℕ; suc)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; _++_; [_])
import Data.Nat.Show as Nat
open import Scotty using (countParams; captureParams; ScottyM)
open import Data.Bool using (T?; true; Bool; false)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Vec using (Vec; _∷_; [])
import Data.List as List
import Data.Vec as Vec
import Scotty
open import Function.Base using (_∘_; id)
import Foreign.Haskell.Pair as Pair
import Text.Lazy as Text
open Scotty using (HttpEncodable)
open HttpEncodable {{...}}

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
infix 15 _⟫
infixr 5 _×_

toFunction : {n : ℕ} → Appliable n → Set → Set
toFunction Mk ret = ret
toFunction (Apply T applies) ret = T → toFunction applies ret

record ArgumentForZero : Set₁ where
  constructor return_through_
  field
    return : Set
    handler : Scotty.ActionM return
    {{returnEncodable}} : HttpEncodable return

record ArgumentForOne : Set₁ where
  constructor receive_return_through_
  field
    param : Set
    return : Set
    handler : param → (Scotty.ActionM return)
    {{paramEncodable}} : HttpEncodable param
    {{returnEncodable}} : HttpEncodable return

infix 3 Get_will_
infix 5 return_through_
infix 4 receive_return_through_

record ArgumentForMultiple (n : ℕ) : Set₁ where
  constructor receive_return_through_
  field
    param : Appliable n
    return : Set
    handler : toFunction param (Scotty.ActionM return)
    {{returnEncodable}} : HttpEncodable return

fromRouteCount : ℕ → Set₁
fromRouteCount 0 = ArgumentForZero
fromRouteCount (suc 0) = ArgumentForOne
fromRouteCount x@(suc n) = ArgumentForMultiple x

data Route : Set₁ where
  Get_will_ : (route : String) → fromRouteCount (countParams route) → Route
  -- Post : (route : String) → (arguments : Appliable (countParams route)) → (body : Set) → (returnType : Set) → toFunction arguments (body → returnType) → Route

apply : ∀ {n : ℕ} → {A : Set} → (arguments : Appliable n) → Vec String n → toFunction arguments A → Scotty.ActionM A
apply Mk _ f = Scotty.ActionM.pure f
apply {_} {A} (Apply X {{i}} x) (param ∷ tail) f = do
  param ← Scotty.captureParam param
  apply x tail (f param)
  where
    open Scotty.ActionM

open Scotty.ActionM using (pure)

toScottyRoute : Route → ScottyM Prim.⊤
toScottyRoute (Get route will arguments)                                       with countParams route | Scotty.getParams route
toScottyRoute (Get route will return returnType through handler)               |                    0 |                  Vec.[] =
  Scotty.get route payload
  where
    open Scotty.ActionM
    payload : Scotty.ActionM Prim.⊤
    payload = do
      value ← handler
      Scotty.text (encode value)
toScottyRoute (Get route will receive param return returnType through handler) |              (suc 0) |              p Vec.∷ [] =
  Scotty.get route payload
  where
    open Scotty.ActionM
    payload : Scotty.ActionM Prim.⊤
    payload = do
      param ← Scotty.captureParam p
      value ← handler param
      Scotty.text (encode value)
toScottyRoute (Get route will receive param return returnType through handler) |        (suc (suc n)) |              paramNames =
  Scotty.get route payload
  where
    open Scotty.ActionM
    payload : Scotty.ActionM Prim.⊤
    payload = do
      value ← apply param paramNames handler
      value ← value
      Scotty.text (encode value)

end : List Route
end = List.[]

_>>_ : Route → List Route → List Route
x >> y = x List.∷ y
