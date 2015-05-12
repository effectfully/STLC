module HMTS.Library.Prelude where

open import Level
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit.Base
open import Data.Bool.Base
open import Data.Nat   as Nat hiding (_≟_)
open import Data.Maybe
open import Data.Product
open import Data.List.Base
open import Category.Monad
open RawMonad  {{...}} public hiding (pure)

instance
  Maybe-monad : ∀ {ℓ} -> RawMonad {ℓ} Maybe
  Maybe-monad = monad

record DecEq {α} (A : Set α) : Set α where
  infix 4 _≟_
  field _≟_ : Decidable (_≡_ {A = A})
open DecEq {{...}} public

instance
  DecEq-ℕ : DecEq ℕ
  DecEq-ℕ = record { _≟_ = Nat._≟_ }

_==_ : ∀ {α} {A : Set α} {{_ : DecEq A}} -> A -> A -> Bool
n == m = ⌊ n ≟ m ⌋

lookup-for : ∀ {α β} {A : Set α} {B : Set β} {{_ : DecEq A}}
           -> A -> List (A × B) -> Maybe B
lookup-for x  []            = nothing
lookup-for x ((y , z) ∷ xs) = if x == y then just z else lookup-for x xs

delete : ∀ {α} {A : Set α} {{_ : DecEq A}} -> A -> List A -> List A
delete x  []      = []
delete x (y ∷ xs) = if x == y then xs else y ∷ delete x xs

nub : ∀ {α} {A : Set α} {{_ : DecEq A}} -> List A -> List A
nub = foldr (λ x r -> x ∷ delete x r) []

≟-refl : ∀ {α} {A : Set α} {{_ : DecEq A}} -> (x : A) -> (x ≟ x) ≡ yes refl
≟-refl x with x ≟ x
... | yes refl = refl
... | no  c    = ⊥-elim (c refl)

dcong : ∀ {α β} {A : Set α} {B : Set β} {x y}
      -> (f : A -> B)
      -> (∀ {x y} -> f x ≡ f y -> x ≡ y)
      -> Dec (x ≡ y)
      -> Dec (f x ≡ f y)
dcong f inj d with d
... | no  p = no (p ∘ inj)
... | yes p = yes (cong f p)

dcong₂ : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} {x y v w}
       -> (f : A -> B -> C)
       -> (∀ {x y} -> f x v ≡ f y w -> x ≡ y × v ≡ w)
       -> Dec (x ≡ y)
       -> Dec (v ≡ w)
       -> Dec (f x v ≡ f y w)
dcong₂ f inj d1 d2 with d1
... | no  p = no (p ∘ proj₁ ∘ inj)
... | yes p with d2
... | no  q = no (q ∘ proj₂ ∘ inj)
... | yes q = yes (cong₂ f p q)

_>>=ᵀ_ : ∀ {α} {A : Set α} {b : A -> Level}
       -> (mx : Maybe A) -> (B : ∀ x -> Set (b x)) -> Set (maybe b Level.zero mx)
nothing >>=ᵀ B = ⊤
just x  >>=ᵀ B = B x

_>>=⊤_ : ∀ {α} {A : Set α} {b : A -> Level} {B : ∀ x -> Set (b x)}
       -> (mx : Maybe A) -> (∀ x -> B x) -> mx >>=ᵀ B
nothing >>=⊤ f = _
just x  >>=⊤ f = f x
