module HMTS.Types where

open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Maybe
open import Data.List as List
open import Data.Vec  hiding (_⊛_)

open import HMTS.Prelude

infixr 1 _⇒_

data Type : Set where
  Var  : ℕ -> Type
  _⇒_ : Type -> Type -> Type

Con : ℕ -> Set
Con = Vec Type

_▻_ : ∀ {n} -> Con n -> Type -> Con (suc n)
Γ ▻ σ = σ ∷ Γ

ftv-all : Type -> List ℕ
ftv-all (Var i) = i ∷ []
ftv-all (σ ⇒ τ) = ftv-all σ List.++ ftv-all τ

ftv : Type -> List ℕ
ftv = nub ∘ ftv-all

_≟ᵀ_ : (σ τ : Type) -> Maybe (σ ≡ τ)
Var i   ≟ᵀ  Var j    with i ≟ j
... | yes r rewrite r = just refl
... | no  _           = nothing
(σ ⇒ τ) ≟ᵀ (σ' ⇒ τ') = cong₂ _⇒_ <$> (σ ≟ᵀ σ') ⊛ (τ ≟ᵀ τ')
_        ≟ᵀ _        = nothing
