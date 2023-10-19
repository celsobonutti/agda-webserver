module JSON where

open import Data.Bool using (Bool)
open import Data.String.Properties
open import Data.Float
open import Data.Nat using (ℕ)
open import Data.List hiding (null)
open import Data.Tree.AVL.Map <-strictTotalOrder-≈
open import Data.String using (String)
open import Foreign.Haskell.Pair using (Pair; fromForeign)
open import Function.Base using (_∘_; id)
open import Data.Product using (map₂)

{-# FOREIGN GHC

import qualified Data.Vector as Vector
import qualified Data.Aeson as Aeson
import Data.Aeson.Key (toText)
import Data.Aeson.KeyMap (toList)
import Data.Scientific (toRealFloat)
import Data.Bifunctor (first)

data InterMediaryValue
  = Null
  | Num Double
  | Bool Bool
  | Array (List InterMediaryValue)
  | Object (List (Text, InterMediaryValue))
  | Str Text

fromAesonValue :: Aeson.Value -> InterMediaryValue
fromAesonValue (Aeson.Object o) = Object (first toText <$> toList o)
fromAesonValue (Aeson.Array a) = Array (Vector.toList a)
fromAesonValue (Aeson.String s) = Str (toText s)
fromAesonValue (Aeson.Number n) = Num (toRealFloat n)
fromAesonValue (Aeson.Bool b) = Bool b
fromAesonValue Aeson.Null = Null

#-}

postulate
  Vector : Set → Set
{-# COMPILE GHC Vector = type Vector #-}

data IntermediaryValue : Set where
  null' : IntermediaryValue
  number' : Float → IntermediaryValue
  bool' : Bool → IntermediaryValue
  array' : List IntermediaryValue → IntermediaryValue
  object' : List (Pair String IntermediaryValue) → IntermediaryValue
  string' : String → IntermediaryValue

{-# COMPILE GHC IntermediaryValue = data IntermediaryValue (Null | Num | Bool | Array | Object | Str) #-}

data JSON : Set where
  null : JSON
  number : Float → JSON
  bool : Bool → JSON
  array : List JSON → JSON
  object : Map JSON → JSON
  string : String → JSON

{-# NON_TERMINATING #-}
convert : IntermediaryValue → JSON
convert null' = null
convert (number' x) = number x
convert (bool' x) = bool x
convert (array' x) = array (Data.List.map convert x)
convert (object' x) = object (fromList (Data.List.map (map₂ convert ∘ fromForeign) x))
convert (string' x) = string x
