module Route where

import Agda.Builtin.Unit as Prim
open import Data.Nat using (ℕ; suc)
open import Data.String using (String)
open import Data.Maybe as Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.List using (List; _++_; [_]; _∷_; [])
import Data.Nat.Show as Nat
open import Scotty using (ScottyM; ActionM)
open import Data.Bool using (T?; true; Bool; false)
open import Relation.Binary.PropositionalEquality hiding ([_])
import Data.List as List
import Data.Vec as Vec
import Scotty
open import Function.Base using (_∘_; id; _|>_; _$_; case_of_)
import Foreign.Haskell.Pair as Pair
import Text.Lazy as Text
import Data.String.Properties as StringProperties
open import Data.HTTP.Encodable
open import Relation.Nullary.Decidable using (True)
open import Data.List.Relation.Unary.Unique.DecSetoid StringProperties.≈-decSetoid using (Unique; unique?)
open import Data.Product using (_×_; _,_; proj₂; proj₁)
open import Route.Parser
open import UnifiesWithTuple
open import Effect.Monad
open RawMonad ⦃...⦄ hiding (return)
open HttpEncodable ⦃...⦄
open import Data.Vec renaming ([] to []̬; _∷_ to _∷̬_; _++_ to _++̬_)
open import Data.String.Properties using (≤-decTotalOrder-≈; <-strictTotalOrder-≈)
open import Data.Tree.AVL.Map <-strictTotalOrder-≈ as Map
import Data.List.Properties as ListProperties

uncurryInput : ∀ {t n} → UnifiesWithTuple t n → Set → Set
uncurryInput (tup {n} {t₁} t₂-unifies) returnType = t₁ → uncurryInput t₂-unifies returnType
uncurryInput (base {t}) returnType = t → returnType

uncurryInputV : ∀ {t n} → UnifiesWithTupleV t n → Set → Set
uncurryInputV (tupL {_} {t} unifies) returnType = List t → uncurryInputV unifies returnType
uncurryInputV (tupO {_} {t} unifies) returnType = Maybe t → uncurryInputV unifies returnType
uncurryInputV (tupC {_} {t} unifies) returnType = t → uncurryInputV unifies returnType
uncurryInputV (baseL {t}) returnType = List t → returnType
uncurryInputV (baseO {t}) returnType = Maybe t → returnType
uncurryInputV (baseC {t}) returnType = t → returnType

decodeAsFailure : ∀ {A}
               → ⦃ HttpEncodable A ⦄
               → String
               → ActionM A
decodeAsFailure {A} ⦃ httpEncodable ⦄ value =
  case HttpEncodable.decode httpEncodable value of λ where
    (just result) → pure result
    nothing → Scotty.throw "Could not decode input"

decodeListAsFailure : ∀ {A}
                → ⦃ HttpEncodable A ⦄
                → List String
                → ActionM (List A)
decodeListAsFailure ⦃ httpEncodable ⦄ [] =
  pure []
decodeListAsFailure ⦃ httpEncodable ⦄ (x ∷ xs) = do
  decodedX ← decodeAsFailure ⦃ httpEncodable ⦄ x
  decodedXS ← decodeListAsFailure ⦃ httpEncodable ⦄ xs
  pure (decodedX ∷ decodedXS)


applyInput : ∀ {n arguments A}
          → ⦃ unifies : UnifiesWithTuple arguments n ⦄
          → Vec String n
          → uncurryInput unifies (ActionM A)
          → ActionM A
applyInput ⦃ base {t} ⦃ httpEncodable ⦄ ⦄ (value ∷̬ []̬) f = do
  decodedValue ← decodeAsFailure ⦃ httpEncodable ⦄ value
  f decodedValue
applyInput ⦃ tup {n} {t₁} ⦃ httpEncodable ⦄ t₂-unifies ⦄ (param ∷̬ params) f = do
  decodedParam ← decodeAsFailure ⦃ httpEncodable ⦄ param
  applyInput ⦃ t₂-unifies ⦄ params (f decodedParam)

applyInputV : ∀ {t s arguments A}
           → ⦃ unifies : UnifiesWithTupleV arguments t ⦄
           → s ≡ List.length t
           → Vec String s
           → Map (List String)
           → uncurryInputV unifies (ActionM A)
           → ActionM A
applyInputV ⦃ unifies = tupC u ⦄ refl (paramName ∷̬ paramNames) params f with Map.lookup params paramName
... | just (value ∷ []) = do
  decodedValue ← decodeAsFailure value
  applyInputV ⦃ u ⦄ refl paramNames params (f decodedValue)
... | just _ = Scotty.throw "Could not decode input"
... | nothing = Scotty.throw "Could not decode input"
applyInputV ⦃ unifies = tupO { t₁ = t } u ⦄ refl (paramName ∷̬ paramNames) params f with Maybe.fromMaybe [] (Map.lookup params paramName)
... | [] =
  applyInputV ⦃ u ⦄ refl paramNames params (f nothing)
... | (value ∷ []) = do
  decodedValue ← decodeAsFailure {t} value
  applyInputV ⦃ u ⦄ refl paramNames params (f (just decodedValue))
... | _ = Scotty.throw "Could not decode input"
applyInputV ⦃ unifies = tupL { t₁ = t } u ⦄ refl (paramName ∷̬ paramNames) params f = do
  decodedValue ← decodeListAsFailure (Maybe.fromMaybe [] (Map.lookup params paramName))
  applyInputV ⦃ u ⦄ refl paramNames params (f decodedValue)
applyInputV ⦃ unifies = baseL ⦄ refl (value ∷̬ []̬) _ f = do
  decodedValue ← decodeAsFailure value
  f decodedValue
applyInputV ⦃ unifies = baseO ⦄ refl (value ∷̬ []̬) _ f = do
  decodedValue ← decodeAsFailure value
  f decodedValue
applyInputV ⦃ unifies = baseC ⦄ refl (value ∷̬ []̬) _ f = do
  decodedValue ← decodeAsFailure value
  f decodedValue

applyPathAndQuery : ∀ {pathSize queryList pathArguments queryArguments s A}
           → ⦃ pathUnifies : UnifiesWithTuple pathArguments pathSize ⦄
           → ⦃ queryUnifies : UnifiesWithTupleV queryArguments queryList ⦄
           → Vec String pathSize
           → s ≡ List.length queryList
           → Vec String s
           → Map (List String)
           → uncurryInput pathUnifies (uncurryInputV queryUnifies (ActionM A))
           → ActionM A
applyPathAndQuery ⦃ pathUnifies = tup {t} ⦃ httpEncodable ⦄ pathUnifies ⦄ ⦃ queryUnifies ⦄ (value ∷̬ xs) proof paranNames params f = do
  decodedValue ← decodeAsFailure ⦃ httpEncodable ⦄ value
  applyPathAndQuery ⦃ pathUnifies ⦄ ⦃ queryUnifies ⦄ xs proof paranNames params (f decodedValue)
applyPathAndQuery ⦃ pathUnifies = base {t} ⦃ httpEncodable ⦄ ⦄ ⦃ queryUnifies ⦄ (value ∷̬ []̬) proof paramNames params f = do
  decodedValue ← decodeAsFailure ⦃ httpEncodable ⦄ value
  applyInputV ⦃ queryUnifies ⦄ proof paramNames params (f decodedValue)


record ParamsForNone : Set₁ where
  constructor return_through_
  field
    return : Set
    handler : Scotty.ActionM return
    ⦃ returnEncodable ⦄ : HttpEncodable return

record ParamsForPathVar (n : ℕ) : Set₁ where
  constructor receive-param_return_through_
  field
    input : Set
    return : Set
    ⦃ returnEncodable ⦄ : HttpEncodable return
    ⦃ unifiesWithTuple ⦄ : UnifiesWithTuple input n
    handler : uncurryInput unifiesWithTuple (ActionM return)

record ParamsForQueryVar (n : List (String × VarType)) : Set₁ where
  constructor receive-query_return_through_
  field
    input : Set
    return : Set
    ⦃ returnEncodable ⦄ : HttpEncodable return
    ⦃ unifiesWithTuple ⦄ : UnifiesWithTupleV input (List.map proj₂ n)
    handler : uncurryInputV unifiesWithTuple (ActionM return)

record ParamsForPathAndQueryVar (n : ℕ) (m : List (String × VarType)) : Set₁ where
  constructor receive-param_and-query_return_through_
  field
    pathParams : Set
    queryParams : Set
    return : Set
    ⦃ returnEncodable ⦄ : HttpEncodable return
    ⦃ unifiesWithTuple ⦄ : UnifiesWithTuple pathParams n
    ⦃ unifiesWithTupleV ⦄ : UnifiesWithTupleV queryParams (List.map proj₂ m)
    handler : uncurryInput unifiesWithTuple (uncurryInputV unifiesWithTupleV (ActionM return))

params-for-get : ℕ → List (String × VarType) → Set₁
params-for-get ℕ.zero [] = ParamsForNone
params-for-get ℕ.zero xs@(_ ∷ _) = ParamsForQueryVar xs
params-for-get x@(suc _) [] = ParamsForPathVar x
params-for-get x@(suc _) xs@(_ ∷ _) = ParamsForPathAndQueryVar x xs


data Route : Set₁ where
  get_will_ : ∀ s → {p : True (validRoute? s)}
                  → params-for-get (countPathVariables s {p})
                                      (makeQueryVariables s {p})
                  → Route


bothSides : ∀ {A B : Set} → (s : List (A × B)) → List.length (List.map proj₁ s) ≡ List.length (List.map proj₂ s)
bothSides {A} {B} s = trans left (sym right)
  where
    left : List.length (List.map proj₁ s) ≡ List.length s
    left = ListProperties.length-map proj₁ s
    right : List.length (List.map proj₂ s) ≡ List.length s
    right = ListProperties.length-map proj₂ s


toScottyRoute : Route → ScottyM Prim.⊤
toScottyRoute (get_will_ s {p} params)
  with countPathVariables s {p} | makeQueryVariables s {p}

toScottyRoute (get route will (return_through_ returnType handler ⦃ returnEncodable ⦄)) | 0 | [] =
  HttpEncodable.encode returnEncodable
    <$> handler
    >>= Scotty.text
    |> Scotty.get (pathPart route)

toScottyRoute (get_will_ route {p} (receive-param_return_through_ inputType returnType ⦃ returnEncodable ⦄ ⦃ unifiesWithTuple ⦄ handler))
              | suc n | [] =
              Scotty.get (pathPart route) $ do
                params ← Scotty.captureParams {route} {p}
                result ← applyInput ⦃ unifiesWithTuple ⦄ (Scotty.replaceVecSize params proof) handler
                Scotty.text (HttpEncodable.encode returnEncodable result)
              where
                postulate
                  -- We know this because of the `with` clause, but Agda can't find it?
                  proof : countPathVariables route {p} ≡ suc n

toScottyRoute (get_will_ route {p} (receive-query_return_through_ inputType returnType ⦃ returnEncodable ⦄ ⦃ unifiesWithTuple ⦄ handler))
              | 0 | (x ∷ xs) = Scotty.get (pathPart route) $ do
                              queryParams ← Scotty.queryParams {route} {p}
                              result ← applyInputV ⦃ unifiesWithTuple ⦄ (bothSides (x ∷ xs)) (Vec.fromList (List.map proj₁ (x ∷ xs))) queryParams handler
                              Scotty.text (HttpEncodable.encode returnEncodable result)


toScottyRoute (get_will_ route {p} (receive-param_and-query_return_through_ pathParams queryParams returnType ⦃ returnEncodable ⦄ ⦃ unifiesWithTuple ⦄ ⦃ unifiesWithTupleV ⦄ handler))
              | suc n | (x ∷ xs) =
              Scotty.get (pathPart route) $ do
                params ← Scotty.captureParams {route} {p}
                queryParams ← Scotty.queryParams {route} {p}
                result ← applyPathAndQuery ⦃ unifiesWithTuple ⦄ ⦃ unifiesWithTupleV ⦄ (Scotty.replaceVecSize params proof) (bothSides (x ∷ xs)) (Vec.fromList (List.map proj₁ (x ∷ xs))) queryParams handler
                Scotty.text (HttpEncodable.encode returnEncodable result)
              where
                postulate
                  -- We know this because of the `with` clause, but Agda can't find it?
                  proof : countPathVariables route {p} ≡ suc n

end : List Route
end = List.[]

