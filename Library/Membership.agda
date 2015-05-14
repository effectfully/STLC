module HMTS.Library.Membership where

open import Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Fin
open import Data.List.Base
open import Data.Vec hiding (_∈_; module _∈_; _++_)

open import HMTS.Library.Prelude

infix 2 _∈_ _∉_ _⊆_ _∈ᵛ_

data _∈_ {α} {A : Set α} (x : A) : List A -> Set α where
  here  : ∀ {xs}   -> x ∈ x ∷ xs
  there : ∀ {xs y} -> x ∈     xs -> x ∈ y ∷ xs

_∉_ : ∀ {α} {A : Set α} -> A -> List A -> Set α
x ∉ xs = ¬ (x ∈ xs)

∈-to-Fin : ∀ {α} {A : Set α} {x} {xs : List A} -> x ∈ xs -> Fin (length xs)
∈-to-Fin  here     = zero
∈-to-Fin (there p) = suc (∈-to-Fin p)

∈-++₁ : ∀ {α} {A : Set α} {x} {xs ys : List A}
      -> x ∈ xs -> x ∈ xs ++ ys
∈-++₁  here     = here
∈-++₁ (there p) = there (∈-++₁ p)

∈-++₂ : ∀ {α} {A : Set α} {x} {ys : List A}
      -> (xs : List A) -> x ∈ ys -> x ∈ xs ++ ys
∈-++₂  []      p = p
∈-++₂ (x ∷ xs) p = there (∈-++₂ xs p)

elim-∈-∷ : ∀ {α} {A : Set α} {x y} {xs ys : List A}
         -> (∀ {x} -> x ∈ xs -> x ∈ ys) -> x ∈ y ∷ xs -> y ∈ ys -> x ∈ ys
elim-∈-∷ f  here     q = q
elim-∈-∷ f (there p) q = f p

_∘∉_ : ∀ {α} {A : Set α} {x y} {xs : List A} -> x ≢ y -> x ∉ xs -> x ∉ y ∷ xs
_∘∉_ p q  here     = p refl
_∘∉_ p q (there r) = q r

_∈?_ : ∀ {α} {A : Set α} {{_ : DecEq A}} -> Decidable (_∈_ {A = A})
y ∈?  []      = no λ()
y ∈? (x ∷ xs) with y ≟ x
... | yes p rewrite p = yes here
... | no  p with y ∈? xs
... | yes q = yes (there q)
... | no  q = no (p ∘∉ q)

_⊆_ : ∀ {α} {A : Set α} -> List A -> List A -> Set α
xs ⊆ ys = ∀ {x} -> x ∈ xs -> x ∈ ys

⊆-refl-++₂ : ∀ {α} {A : Set α} {xs : List A} ys -> xs ⊆ ys ++ xs
⊆-refl-++₂  []      p = p
⊆-refl-++₂ (y ∷ ys) p = there (⊆-refl-++₂ ys p)

⊆-∷ : ∀ {α} {A : Set α} {x} {xs ys : List A} -> xs ⊆ ys -> x ∷ xs ⊆ x ∷ ys
⊆-∷ sub  here     = here
⊆-∷ sub (there p) = there (sub p)

_⊆?_ : ∀ {α} {A : Set α} {{_ : DecEq A}} -> Decidable (_⊆_ {A = A})
[]       ⊆? ys = yes λ()
(x ∷ xs) ⊆? ys with x ∈? ys
... | no  p = no λ r -> p (r here)
... | yes p with xs ⊆? ys
... | no  q = no λ r -> q (r ∘ there)
... | yes q = yes λ r -> elim-∈-∷ q r p

----------

data _∈ᵛ_ {α} {A : Set α} (x : A) : ∀ {n} -> Vec A n -> Set α where
  here  : ∀ {n} {xs : Vec A n}     -> x ∈ᵛ x ∷ xs
  there : ∀ {n} {xs : Vec A n} {y} -> x ∈ᵛ     xs -> x ∈ᵛ y ∷ xs

lookup-in : ∀ {α n} {A : Set α} i -> (xs : Vec A n) -> lookup i xs ∈ᵛ xs
lookup-in  zero   (x ∷ xs) = here
lookup-in (suc i) (x ∷ xs) = there (lookup-in i xs)

∈ᵛ-to-Fin : ∀ {α n} {A : Set α} {x} {xs : Vec A n} -> x ∈ᵛ xs -> Fin n
∈ᵛ-to-Fin  here     = zero
∈ᵛ-to-Fin (there p) = suc (∈ᵛ-to-Fin p)

∈ᵛ-to-Fin∘lookup-in : ∀ {α n} {A : Set α} i (xs : Vec A n)
                    -> ∈ᵛ-to-Fin (lookup-in i xs) ≡ i
∈ᵛ-to-Fin∘lookup-in  zero   (x ∷ xs) = refl
∈ᵛ-to-Fin∘lookup-in (suc i) (x ∷ xs) = cong suc (∈ᵛ-to-Fin∘lookup-in i xs)

∈ᵛ-to-∈ : ∀ {α n} {A : Set α} {x} {xs : Vec A n} -> x ∈ᵛ xs -> x ∈ toList xs
∈ᵛ-to-∈  here     = here
∈ᵛ-to-∈ (there p) = there (∈ᵛ-to-∈ p)
