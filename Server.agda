{-# OPTIONS --guardedness #-}
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
open import Data.Nat
import Data.List as List

useRoutes' : (x : List Route) → {{List.length x > 0}} → Scotty.ScottyM Prim.⊤
useRoutes' (x ∷ y) =
  List.foldl (λ eff route → eff >> Route.toScottyRoute route) (Route.toScottyRoute x) y
  where
    open Scotty.ScottyM

start : (port : ℕ) → {{port ∸ 65535 ≡ 0}} → (x : List Route) → {{List.length x > 0}} → IO ⊤
start port routes =
  Scotty.scotty port (useRoutes' routes)
