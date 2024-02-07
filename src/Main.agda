module Main where

open import Data.String hiding (_<_; _≤_)
open import Data.Nat.Base
open import Agda.Builtin.FromString
open import Data.String.Literals
import Data.Vec as Vec
import Data.Nat.Show as Nat
import Data.Char as Char
import Agda.Builtin.Unit as PrimUnit
open import Data.Unit.Polymorphic.Base
open import Function.Base using (_∘_; id; case_of_)
open import IO.Base using (IO)
import Scotty
open import Route
open import Route.Parser
open import Data.Product using (_×_; _,_)
open import UnifiesWithTuple
open import Prelude
open import Effect.Monad
open RawMonad ⦃...⦄
import Server


instance
  _ : IsString String
  _ = isString

handler : ℕ → String → Scotty.ActionM String
handler id name =
  pure ("Hello, " ++ name ++ "!\n" ++
                       "Your id is " ++ Nat.show id ++ ".")

handler₁ : {A B : Set} → A → B → Scotty.ActionM A
handler₁ id _ = pure id

handler₂ : String → ℕ → Maybe String → Scotty.ActionM String
handler₂ thing n nothing = pure thing
handler₂ thing n (just name) = pure (thing ++ name)

handler₃ : ∀ {A} → A → Scotty.ActionM A
handler₃ = pure

first : Route
first = get "/:memes/:xd" will
        receive-param String × String
        return String
        through handler₁

second : Route
second = get "/user" will
        -- receive-query String × List String
        return String
        through (pure "Hello, world!")

third : Route
third = get "/text/:memes?id&name?" will
        receive-param String
        and-query ℕ × Maybe String
        return String
        through handler₂


main' : IO ⊤
main' = Server.start 4000 routes'
  where
    routes' : List Route
    routes' =
      second
      ∷ third
      ∷ []
      where open Route.Route

main : IO.Base.Main
main = IO.Base.run main'
