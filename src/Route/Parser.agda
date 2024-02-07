module Route.Parser where

open import Data.Char using (_≟_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (toℕ)
open import Data.List using (length; splitAt; drop; reverse; findIndex)
open import Data.List.Relation.Unary.All using (All; all?) renaming (reduce to reduceAll)
open import Data.List.Membership.DecPropositional _≟_ using (_∈_; _∈?_)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Nat.Properties using (_>?_)
open import Data.Nat using (_>_)
open import Data.Product using (_×_; _,_; proj₁; proj₂) renaming (map to ×-map; map₂ to ×-map₂)
open import Data.String using (toList; fromList; linesBy) renaming (_≟_ to _≟ₛ_; length to lengthₛ)
open import Level renaming (zero to ℓ₀)
open import Prelude
open import Relation.Binary renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (True; _×-dec_; Dec; yes; no; toWitness; fromWitness)
open import Relation.Unary using (Decidable; Pred)
open import UnifiesWithTuple

alphaNumChars : List Char
alphaNumChars =
  'a' ∷ 'b' ∷ 'c' ∷ 'd' ∷ 'e' ∷ 'f' ∷ 'g' ∷ 'h' ∷ 'i' ∷ 'j' ∷ 'k' ∷ 'l' ∷ 'm' ∷ 'n' ∷ 'o' ∷ 'p' ∷ 'q' ∷ 'r' ∷ 's' ∷ 't' ∷ 'u' ∷ 'v' ∷ 'w' ∷ 'x' ∷ 'y' ∷ 'z' ∷
  'A' ∷ 'B' ∷ 'C' ∷ 'D' ∷ 'E' ∷ 'F' ∷ 'G' ∷ 'H' ∷ 'I' ∷ 'J' ∷ 'K' ∷ 'L' ∷ 'M' ∷ 'N' ∷ 'O' ∷ 'P' ∷ 'Q' ∷ 'R' ∷ 'S' ∷ 'T' ∷ 'U' ∷ 'V' ∷ 'W' ∷ 'X' ∷ 'Y' ∷ 'Z' ∷
  '0' ∷ '1' ∷ '2' ∷ '3' ∷ '4' ∷ '5' ∷ '6' ∷ '7' ∷ '8' ∷ '9' ∷ []

otherChars : List Char
otherChars =
  '.' ∷ '-' ∷ '_' ∷ '~' ∷ '!' ∷ '&' ∷ '\'' ∷ '(' ∷ ')' ∷ '*' ∷ '+' ∷ ',' ∷ ';' ∷ '=' ∷ ':' ∷ '@' ∷ []

data IsAlphaNum : Pred Char ℓ₀ where
  alphaNum : ∀ {c} → c ∈ alphaNumChars → IsAlphaNum c

alphaNum? : Decidable IsAlphaNum
alphaNum? c with c ∈? alphaNumChars
... | yes p = yes (alphaNum p)
... | no ¬p = no λ { (alphaNum p) → ¬p p }

data ValidPathChar : Pred Char ℓ₀ where
  alphaNum : ∀ {c} → IsAlphaNum c → ValidPathChar c
  other : ∀ {c} → c ∈ otherChars → ValidPathChar c

validPathChar? : Decidable ValidPathChar
validPathChar? c with c ∈? otherChars
... | yes others = yes (other others)
... | no ¬others with alphaNum? c
... | yes alphaN = yes (alphaNum alphaN)
... | no ¬alphaNum = no λ { (other others) → ¬others others
                          ; (alphaNum alphaN) → ¬alphaNum alphaN
                          }

data ValidPathPart : Pred String ℓ₀ where
  validPath : ∀ {x} → All ValidPathChar (toList x) → ValidPathPart x

validPathPart? : Decidable ValidPathPart
validPathPart? x with all? validPathChar? (toList x)
... | yes valid = yes (validPath valid)
... | no ¬valid = no (λ { (validPath valid) → ¬valid valid })

data _StartsWith_ : REL String Char ℓ₀ where
  starts : ∀ {c s} → List.head (toList s) ≡ (just c) → s StartsWith c

_≟ₘ_ : (x x₁ : Maybe.Maybe Char.Char) → Dec (x ≡ x₁)
_≟ₘ_ = ≡-dec _≟_

_startsWith?_ : Decidable₂ _StartsWith_
s startsWith? c with List.head (toList s) ≟ₘ (just c)
... | yes start = yes (starts start)
... | no ¬start = no λ {(starts start) → ¬start start}

lastN : ∀ {A : Set} → ℕ → List A → List A
lastN n x = proj₂ (splitAt (length x ∸ n) x)

lastNₛ : ℕ → String → String
lastNₛ n x = fromList (lastN n (toList x))

data _EndsWith_ : Rel String ℓ₀ where
  endsWith : ∀ {xs ys} → fromList (lastN (length (toList ys)) (toList xs)) ≡ ys → xs EndsWith ys

dropₛ : ℕ → String → String
dropₛ n = fromList ∘ reverse ∘ drop n ∘ reverse ∘ toList

_endsWith?_ : Decidable₂ _EndsWith_
_endsWith?_ xs ys with fromList (lastN (length (toList ys)) (toList xs)) ≟ₛ ys
... | yes equal = yes (endsWith equal)
... | no ¬equal = no λ {(endsWith equal) → ¬equal equal}

test : (x : Char) → {True (validPathChar? x)} → Char
test x = x

test₁ : (x : String) → {True (x startsWith? ':')} → String
test₁ x = x

data _Is_ : Rel Char ℓ₀ where
  is-char : ∀ {c d} → c ≡ d → c Is d

_is?_ : Decidable₂ _Is_
c is? d with c ≟ d
... | yes is  = yes (is-char is)
... | no isnt = no λ {(is-char is) → isnt is}

AllAlphaNum : Pred String ℓ₀
AllAlphaNum x = All IsAlphaNum (toList x)

data SimpleQuery : Pred String ℓ₀ where
  simple : ∀ {s} → AllAlphaNum s → lengthₛ s > 0 → SimpleQuery s

data MultipleQuery : Pred String ℓ₀ where
  multiple : ∀ {s} → s EndsWith "[]" → SimpleQuery (dropₛ 2 s) → MultipleQuery s

data OptionalQuery : Pred String ℓ₀ where
  optional : ∀ {s} → s EndsWith "?" → SimpleQuery (dropₛ 1 s) → OptionalQuery s

simple? : Decidable SimpleQuery
simple? s with all? alphaNum? (toList s) | lengthₛ s >? 0
... | yes alpha | yes l = yes (simple alpha l)
... | no ¬alpha | _     = no λ { (simple alpha _) → ¬alpha alpha }
... | yes _     | no ¬l = no λ { (simple _ l) → ¬l l }

multiple? : Decidable MultipleQuery
multiple? s with s endsWith? "[]" | simple? (dropₛ 2 s)
... | yes brackets | yes alpha = yes (multiple brackets alpha)
... | no ¬brackets | _         = no λ { (multiple brackets _) → ¬brackets brackets }
... | yes _        | no ¬alpha = no λ { (multiple _ alpha) → ¬alpha alpha }

optional? : Decidable OptionalQuery
optional? s with s endsWith? "?" | simple? (dropₛ 1 s)
... | yes question | yes alpha = yes (optional question alpha)
... | no ¬question | _         = no λ { (optional question _) → ¬question question }
... | yes _        | no ¬alpha = no λ { (optional _ alpha) → ¬alpha alpha }

data ValidQueryPart : Pred String ℓ₀ where
  multiple : ∀ {s} → MultipleQuery s → ValidQueryPart s
  optional : ∀ {s} → OptionalQuery s → ValidQueryPart s
  simple : ∀ {s} → SimpleQuery s → ValidQueryPart s

validQueryPart? : Decidable ValidQueryPart
validQueryPart? s with multiple? s
... | yes m = yes (multiple m)
... | no ¬m with optional? s
... | yes o = yes (optional o)
... | no ¬o with simple? s
... | yes s = yes (simple s)
... | no ¬s = no λ { (multiple m) → ¬m m
                   ; (optional o) → ¬o o
                   ; (simple s)   → ¬s s
                   }

splitByChar : String → Char → String × String
splitByChar s c = ×-map fromList fromList (fn list index)
  where
    list = toList s
    index = findIndex (_is? c) list
    fn : List Char → Maybe (Data.Fin.Fin (lengthₛ s)) → List Char × List Char
    fn x nothing = x , []
    fn x (just index) = ×-map₂ (drop 1) (splitAt (toℕ index) x)

data ValidPath : Pred String ℓ₀ where
  allValid : ∀ {s} → All ValidPathPart (linesBy (_is? '/') s) → ValidPath s

data ValidQuery : Pred String ℓ₀ where
  allValidQ : ∀ {s} → All ValidQueryPart (linesBy (_is? '&') s) → ValidQuery s

validPath? : Decidable ValidPath
validPath? s with all? validPathPart? (linesBy (_is? '/') s)
... | yes all = yes (allValid all)
... | no isnt = no λ {(allValid is) → isnt is}

validQuery? : Decidable ValidQuery
validQuery? s with all? validQueryPart? (linesBy (_is? '&') s)
... | yes all = yes (allValidQ all)
... | no isnt = no λ {(allValidQ is) → isnt is}

test₂ : (x : String) → {True (validPath? x)} → String
test₂ x = x

_ : String
_ = test₂ "/memes/basimga/xd/xosdeeeeeee///"

test₃ : (x : String) → (y : String) → {True (x endsWith? y)} → String
test₃ x y = x

test₄ : (x : String) → (y : String) → {True (validQuery? x ×-dec validPath? y)} → String × String
test₄ x y = x , y

_ : String × String
_ = test₄ "memes&bozzano&xd?&xosde[]" "/memes/basimga/xd/bozzano"

pathPart : String → String
pathPart s = (proj₁ (splitByChar s '?'))

queryPart : String → String
queryPart s = (proj₂ (splitByChar s '?'))

data ValidRoute : Pred String ℓ₀ where
  validRoute : ∀ {s} → ValidPath (pathPart s) → ValidQuery (queryPart s) → ValidRoute s

queryProof : ∀ {s} → ValidRoute s → ValidQuery (queryPart s)
queryProof (validRoute _ q) = q

validRoute? : Decidable ValidRoute
validRoute? s with validPath? (pathPart s) | validQuery? (queryPart s)
... | yes path | yes query = yes (validRoute path query)
... | no ¬path | _         = no λ {(validRoute path _) → ¬path path}
... | yes _    | no ¬query = no λ {(validRoute _ query) → ¬query query}

test₅ : (x : String) → {True (validRoute? x)} → String
test₅ x = x

_ : String
_ = test₅ "/memes/basimga/xd?memes&bozzano&xd?&xosde[]"

countPathVariables : ∀ s → {True (validRoute? s)} → ℕ
countPathVariables s = length (List.filter (_startsWith? ':') (linesBy (_is? '/') (pathPart s)))

makeQueryVariables : ∀ s → {True (validRoute? s)} → List (String × VarType)
makeQueryVariables s {p} with validQuery? (queryPart s)
... | yes (allValidQ p) = reduceAll (λ ep → makeVar ep) p
  where
    makeVar : ∀ {s} → ValidQueryPart s → (String × VarType)
    makeVar (multiple (multiple _ (simple {x} _ _))) = x , listV
    makeVar (optional (optional _ (simple {x} _ _))) = x , optional
    makeVar (simple (simple {x} _ _)) = x , common
... | no ¬-validQuery = ⊥-elim (¬-validQuery (queryProof (toWitness p)))
