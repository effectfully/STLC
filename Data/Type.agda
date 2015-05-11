module HMTS.Data.Type where

open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Maybe
open import Data.List
open import Data.Vec  hiding (_⊛_; _++_)

open import HMTS.Utilities.Prelude

infixr 2 _⇒_
infixl 5 _▻_ _▻▻_ _▻ᵛ_

data Type : Set where
  Var  : ℕ -> Type
  _⇒_ : Type -> Type -> Type

Con : Set
Con = List Type

_▻_ : Con -> Type -> Con
Γ ▻ σ = σ ∷ Γ

_▻▻_ : Con -> Con -> Con
_▻▻_ = flip _++_

Conᵛ : ℕ -> Set
Conᵛ = Vec Type

_▻ᵛ_ : ∀ {n} -> Conᵛ n -> Type -> Conᵛ (suc n)
Γ ▻ᵛ σ = σ ∷ Γ

ftv-all : Type -> List ℕ
ftv-all (Var i) = i ∷ []
ftv-all (σ ⇒ τ) = ftv-all σ ++ ftv-all τ

ftv : Type -> List ℕ
ftv = nub ∘ ftv-all

_≟ᵀ_ : (σ τ : Type) -> Maybe (σ ≡ τ)
Var i   ≟ᵀ  Var j    with i ≟ j
... | yes r rewrite r = just refl
... | no  _           = nothing
(σ ⇒ τ) ≟ᵀ (σ' ⇒ τ') = cong₂ _⇒_ <$> (σ ≟ᵀ σ') ⊛ (τ ≟ᵀ τ')
_        ≟ᵀ _        = nothing
