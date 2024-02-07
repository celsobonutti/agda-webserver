module Scotty where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String; wordsBy)
import IO.Primitive as Prim
import Agda.Builtin.Unit as Prim
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Vec using (Vec)
import Data.Vec as Vec
import Data.String as String
open import Data.List using (List)
open import Agda.Builtin.FromString
open import Foreign.Haskell.Pair using (Pair; snd; fst)
import Data.Char as Char
open import Data.Char using (Char)
open import IO.Base using (IO)
open import Data.Nat.Base
import Data.List.Base as List
open import Data.List hiding (wordsBy; _++_)
open import Function.Base using (_∘_; id)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Bool using (T?; true; Bool; false)
open import Data.Unit.Polymorphic.Base
import Text.Lazy as Text
open import Text.Lazy using (LazyString)
open import Data.String.Instances
import Data.String.Properties as StringProperties
open import Data.List.Relation.Unary.Unique.DecSetoid StringProperties.≈-decSetoid using (Unique; unique?)
open import Relation.Nullary.Decidable using (True; _×-dec_; Dec)
open import Data.Nat.Properties using (_≤?_; _≥?_; _≟_)
open import Data.Sum using (_⊎_)
open import Effect.Monad using (RawMonad)
open RawMonad ⦃...⦄
open import Effect.Applicative using (RawApplicative)
open import Effect.Functor using (RawFunctor)
open import Data.HTTP.Encodable
open import Route.Parser
open import Data.List.Instances
open import Data.Vec.Instances
open import IO.Instances
open import IO.Base using (lift)
open import Data.Vec renaming (map to map-v)
open import Data.String.Properties using (≤-decTotalOrder-≈; <-strictTotalOrder-≈)
open import Data.Tree.AVL.Map <-strictTotalOrder-≈

{-# FOREIGN GHC

import Web.Scotty
import Web.Scotty.Internal.Types
import Data.ByteString
import qualified Data.Text.Lazy as LT
import qualified Data.Text as T
import Control.Exception.Base hiding (throw)

newtype DecodeError = DecodeError T.Text

instance Show DecodeError where
  show _ = "DecodeError"

instance Exception DecodeError

#-}

Param : Set
Param = Pair String String

postulate
  ScottyM : Set → Set
  ActionM : Set → Set
  RoutePattern : Set
  Capture : String → RoutePattern
  get' : RoutePattern → ActionM Prim.⊤ → ScottyM Prim.⊤
  scotty' : ℕ → ScottyM Prim.⊤ → Prim.IO Prim.⊤
  text' : Text.Lazy → ActionM Prim.⊤
  throw : {A : Set} → String → ActionM A
  captureParams' : ActionM (List Param)
  queryParams' : ActionM (List Param)


{-# COMPILE GHC ActionM = type ActionM #-}
{-# COMPILE GHC ScottyM = type ScottyM #-}
{-# COMPILE GHC RoutePattern = type RoutePattern #-}
{-# COMPILE GHC Capture = Capture #-}
{-# COMPILE GHC get' = get #-}
{-# COMPILE GHC scotty' = \p -> scotty (fromIntegral p) #-}
{-# COMPILE GHC text' = text #-}
{-# COMPILE GHC throw = \_ s -> throw (DecodeError s) #-}
{-# COMPILE GHC captureParams' = captureParams #-}
{-# COMPILE GHC queryParams' = queryParams #-}

module ActionM where
  postulate
    _>>=ₐ_ : { A B : Set } → ActionM A → (A → ActionM B) → ActionM B
    _<*>ₐ_ : { A B : Set } → ActionM (A → B) → ActionM A → ActionM B
    _<$>ₐ_ : { A B : Set } → (A → B) → ActionM A → ActionM B
    pureₐ : { A : Set } → A → ActionM A
  {-# COMPILE GHC _>>=ₐ_ = \_ _ -> (>>=) #-}
  {-# COMPILE GHC pureₐ = \_ -> pure #-}
  {-# COMPILE GHC _<$>ₐ_ = \_ _ -> fmap #-}
  {-# COMPILE GHC _<*>ₐ_ = \_ _ -> (<*>) #-}


module ScottyM where
  postulate
    _>>=ₛ_ : { A B : Set } → ScottyM A → (A → ScottyM B) → ScottyM B
    _<*>ₛ_ : { A B : Set } → ScottyM (A → B) → ScottyM A → ScottyM B
    _<$>ₛ_ : { A B : Set } → (A → B) → ScottyM A → ScottyM B
    pureₛ : { A : Set } → A → ScottyM A
  {-# COMPILE GHC _>>=ₛ_ = \_ _ -> (>>=) #-}
  {-# COMPILE GHC pureₛ = \_ -> pure #-}
  {-# COMPILE GHC _<$>ₛ_ = \_ _ -> fmap #-}
  {-# COMPILE GHC _<*>ₛ_ = \_ _ -> (<*>) #-}


instance
  actionRawFunctor : RawFunctor ActionM
  actionRawFunctor = record
    { _<$>_ = ActionM._<$>ₐ_
    }

  actionRawApp : RawApplicative ActionM
  actionRawApp = record
    { _<*>_ = ActionM._<*>ₐ_
    ; pure = ActionM.pureₐ
    ; rawFunctor = actionRawFunctor
    }

  actionRawMonad : RawMonad ActionM
  actionRawMonad = record
    { _>>=_ = ActionM._>>=ₐ_
    ; rawApplicative = actionRawApp
    }

  scottyRawFunctor : RawFunctor ScottyM
  scottyRawFunctor = record
    { _<$>_ = ScottyM._<$>ₛ_
    }

  scottyRawApp : RawApplicative ScottyM
  scottyRawApp = record
    { _<*>_ = ScottyM._<*>ₛ_
    ; pure = ScottyM.pureₛ
    ; rawFunctor = scottyRawFunctor
    }

  scottyRawMonad : RawMonad ScottyM
  scottyRawMonad = record
    { _>>=_ = ScottyM._>>=ₛ_
    ; rawApplicative = scottyRawApp
    }


get : String → ActionM Prim.⊤ → ScottyM Prim.⊤
get = get' ∘ Capture

text : String → ActionM Prim.⊤
text = text' ∘ Text.fromStrict

scotty : (port : ℕ) → {True (port ≤? 65536)} → ScottyM Prim.⊤ → IO ⊤
scotty port action = do
  lift (scotty' port action)
    >>= λ _ → pure tt

replaceVecSize : ∀ {n m : ℕ} {A : Set} → Vec A n → (n ≡ m) → Vec A m
replaceVecSize xs refl = xs

accumQueryParams : List Param → Map (List String)
accumQueryParams = List.foldr (λ param → insertWith (fst param)
                                 λ current → (snd param) ∷ Data.Maybe.fromMaybe [] current)
                              empty

queryParams : ∀ {route}
            → {True (validRoute? route)}
            → ActionM (Map (List String))
queryParams = do
  params ← queryParams'
  pure (accumQueryParams params)

captureParams : {route : String}
  → {p : True (validRoute? route)}
  → ActionM (Vec String (countPathVariables route {p}))
captureParams {route} {p = p} = do
  params ← captureParams'
  pure (map-v (snd) (Vec.reverse (replaceVecSize (Vec.fromList params) (sameSize params))))
  where
    postulate
      sameSize : (params : List Param) → List.length params ≡ countPathVariables route {p}
