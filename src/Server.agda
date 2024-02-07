module Server where

import Route
import Agda.Builtin.Unit as Prim
open import Route using (Route)
import Scotty
open import Data.Unit.Polymorphic.Base
open import Data.List.NonEmpty using (List⁺) renaming (_∷_ to _⁺∷_)
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])
open import IO.Base using (IO)
open import Data.Nat.Properties using (_≤?_; _>?_)
open import Relation.Nullary.Decidable using (True)
open import Data.Nat
import Data.List as List
open import Effect.Monad
open RawMonad ⦃ ... ⦄

useRoutes' : (x : List Route) → {True (List.length x >? 0)} → Scotty.ScottyM Prim.⊤
useRoutes' (x ∷ y) =
  List.foldl (λ eff route → eff >> Route.toScottyRoute route) (Route.toScottyRoute x) y

start : (port : ℕ) → {True (port ≤? 65536)} → (x : List Route) → {True (List.length x >? 0)} → IO ⊤
start port {p} routes {r} =
  Scotty.scotty port {p} (useRoutes' routes {r})
