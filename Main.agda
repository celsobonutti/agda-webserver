{-# OPTIONS --guardedness #-}

module Main where

open import Data.Bool using (T?; true; Bool; false)
open import Data.String hiding (_<_; _≤_)
open import Data.Nat.Base
import IO.Primitive as Prim
open import IO.Finite using (putStrLn)
open import IO.Base using (IO; Main; run; lift)
open import Data.Nat
open import Agda.Builtin.FromString
open import Data.String.Literals
open import Data.Vec using (Vec) renaming (_∷_ to _V∷_; [] to V[])
import Data.Vec as Vec
open import Relation.Nullary.Decidable using (True)
open import Data.Fin hiding (lift; _≤_; _-_)
import Data.Nat.Show as Nat
open import Data.Maybe using (just; Maybe; nothing)
open import Relation.Binary.PropositionalEquality hiding ([_])
import Data.List.Base as List
open import Data.List hiding (wordsBy; _++_)
import Data.Char as Char
open import Data.Char using (Char)
import Agda.Builtin.Unit as PrimUnit
open import Data.Unit.Polymorphic.Base
import Data.Char.Properties as Char using (_≟_)
open import Function.Base using (_∘_; id)
open import Agda.Primitive
import Scotty
import Text.Lazy as Text
open import Scotty hiding (isParameter; splitPaths; countParams; get)
open import Text.Lazy using (LazyString)
open import Server
open import Route
open import JSON


instance
  StringIsString : IsString String
  StringIsString = isString

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
  charEncodable = record { encode = λ _ → "" ; decode = λ _ → nothing }

handler : ℕ → String → Scotty.ActionM String
handler id name =
  Scotty.ActionM.pure ("Hello, " ++ name ++ "!\n" ++
                       "Your id is " ++ Nat.show id ++ ".")

handler₁ : ℕ → Scotty.ActionM ℕ
handler₁ id = Scotty.ActionM.pure (suc id)

handler₂ : Scotty.ActionM String
handler₂ = Scotty.ActionM.pure "Hello, world!"

main' : IO ⊤
main' = Server.start 4000 routes' {{s≤s z≤n}}
  where
    routes' : List Route
    routes' = do
      Get "/user/:id/:name" will receive ⟪ ℕ × String ⟫
                                 return String
                                 through handler

      Get "/user/:id" will receive ℕ
                           return ℕ
                           through handler₁

      Get "/user" will return String
                       through handler₂
      end
      where open Route.Route


main : Main
main =
  run main'
