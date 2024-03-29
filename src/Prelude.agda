module Prelude where

open import Data.List using (_∷_; []; [_]) public
open import Data.Nat.Base using (_+_; _∸_; _*_; suc; zero) public
open import Data.Maybe using (just; nothing) public
open import Data.String using (String) public
open import Data.Nat using (ℕ) public
open import Data.Char using (Char) public
open import Data.Float using (Float) public
open import Data.Bool using (T?; true; false) public
import Data.Char
import Data.String
import Data.Nat
import Data.Maybe
open import Function.Base using (_∘_; id) public
import Data.List
import Data.Bool
import Data.Float
open import Data.String using (wordsBy)
import Data.String.Properties as StringProperties
open import Data.List.Relation.Unary.Unique.DecSetoid StringProperties.≈-decSetoid using (Unique; unique?)
open import Relation.Nullary.Decidable using (True; False)
open import Effect.Monad using (RawMonad; RawMonadZero; RawMonadPlus)
open import Data.List.NonEmpty using (List⁺; _∷⁺_) public
open import Data.Sum public
open import Data.Empty public hiding (⊥-elim)
open import Data.Product using (_×_; uncurry) public

module String = Data.String
module Nat = Data.Nat
module Maybe = Data.Maybe
module List = Data.List
module Char = Data.Char
module Bool = Data.Bool
module Float = Data.Float

List = List.List
Maybe = Maybe.Maybe
Bool = Bool.Bool
