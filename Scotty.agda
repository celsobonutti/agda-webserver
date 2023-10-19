{-# OPTIONS --guardedness #-}
module Scotty where

open import Data.Nat using (ℕ)
open import Data.String using (String; wordsBy)
import IO.Primitive as Prim
import Agda.Builtin.Unit as Prim
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Vec using (Vec)
import Data.Vec as Vec
import Data.String as String
open import Data.List using (List)
open import Agda.Builtin.FromString
open import Foreign.Haskell.Pair using (Pair)
import Data.Char as Char
open import Data.Char using (Char)
open import IO.Base using (IO)
open import Data.Nat.Base
import Data.List.Base as List
open import Data.List hiding (wordsBy; _++_)
open import Function.Base using (_∘_; id)
open import Data.Bool using (T?; true; Bool; false)
open import Data.Unit.Polymorphic.Base
import Text.Lazy as Text
open import Text.Lazy using (LazyString)

{-# FOREIGN GHC

import Web.Scotty
import Web.Scotty.Internal.Types
import Data.ByteString
import qualified Data.Text.Lazy as LT
import qualified Data.Text as T

captureParam' :: LT.Text -> ActionM T.Text
captureParam' = captureParam

#-}

Param : Set
Param = Pair Text.Lazy Text.Lazy

postulate
  ScottyM : Set → Set
  ActionM : Set → Set
  RoutePattern : Set
  Capture : Text.Lazy → RoutePattern
  get : RoutePattern → ActionM Prim.⊤ → ScottyM Prim.⊤
  scotty' : ℕ → ScottyM Prim.⊤ → Prim.IO Prim.⊤
  text' : Text.Lazy → ActionM Prim.⊤
  raise : {A : Set} → Text.Lazy → ActionM A
  captureParams' : ActionM (List Param)
  captureParam : Text.Lazy → ActionM String

{-# COMPILE GHC ActionM = type ActionM #-}
{-# COMPILE GHC ScottyM = type ScottyM #-}
{-# COMPILE GHC RoutePattern = type RoutePattern #-}
{-# COMPILE GHC Capture = Capture #-}
{-# COMPILE GHC get = get #-}
{-# COMPILE GHC scotty' = \p -> scotty (fromIntegral p) #-}
{-# COMPILE GHC text' = text #-}
{-# COMPILE GHC raise = \_ -> raise #-}
{-# COMPILE GHC captureParams' = captureParams #-}
{-# COMPILE GHC captureParam = captureParam' #-}

module ActionM where
  postulate
    _>>=_ : { A B : Set } → ActionM A → (A → ActionM B) → ActionM B
    _>>_ : { A B : Set } → ActionM A → ActionM B → ActionM B
    pure : { A : Set } → A → ActionM A
  {-# COMPILE GHC _>>=_ = \_ _ -> (>>=) #-}
  {-# COMPILE GHC _>>_ = \_ _ -> (>>) #-}
  {-# COMPILE GHC pure = \_ -> pure #-}

module ScottyM where
  postulate
    _>>=_ : { A B : Set } → ScottyM A → (A → ScottyM B) → ScottyM B
    _>>_ : { A B : Set } → ScottyM A → ScottyM B → ScottyM B
    pure : { A : Set } → A → ScottyM A
  {-# COMPILE GHC _>>=_ = \_ _ -> (>>=) #-}
  {-# COMPILE GHC _>>_ = \_ _ -> (>>) #-}
  {-# COMPILE GHC pure = \_ -> pure #-}

text : String → ActionM Prim.⊤
text = text' ∘ Text.fromStrict

scotty : (port : ℕ) → {{port ∸ 65535 ≡ 0}} → ScottyM Prim.⊤ → IO ⊤
scotty port action = do
  lift (scotty' port action)
    >>= λ _ → pure tt
  where open IO.Base

isParameter : String → Bool
isParameter = isParameter' ∘ String.toList
  where
  isParameter' : List Char → Bool
  isParameter' (':' ∷ _) = true
  isParameter' _ = false

splitPaths : String → List String
splitPaths = wordsBy ('/' Char.≟_)

getParams' : String → List String
getParams' = List.filter (T? ∘ isParameter) ∘ splitPaths

countParams : String → ℕ
countParams = List.length ∘ getParams'

getParams : (route : String) → Vec String (countParams route)
getParams = Vec.map (String.fromList ∘ dropDoubleCollon ∘ String.toList) ∘ Vec.fromList ∘ getParams'
  where dropDoubleCollon : List Char → List Char
        dropDoubleCollon (':' ∷ tail) = dropDoubleCollon tail
        dropDoubleCollon x = x

replaceVecSize : ∀ {n m : ℕ} {A : Set} → Vec A n → (n ≡ m) → Vec A m
replaceVecSize xs refl = xs

captureParams : {route : String} → ActionM (Vec Param (countParams route))
captureParams {route} = do
  params ← captureParams'
  pure (replaceVecSize (Vec.fromList params) (sameSize params))
  where
    open ActionM
    postulate
      sameSize : (params : List Param) → List.length params ≡ countParams route
