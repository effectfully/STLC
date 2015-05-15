module STLC.Data.Type where

open import Function
open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Base
open import Data.Product
open import Data.List.Base
open import Data.Vec hiding (_⊛_; _++_)

open import STLC.Utilities.Prelude

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

Var-inj : ∀ {i j} -> Var i ≡ Var j -> i ≡ j
Var-inj refl = refl

⇒-inj : ∀ {σ τ σ' τ'} -> (σ ⇒ τ) ≡ (σ' ⇒ τ') -> σ ≡ σ' × τ ≡ τ'
⇒-inj refl = refl , refl

_≟ᵀ_ : Decidable (_≡_ {A = Type})
Var i   ≟ᵀ  Var j    = dcong Var Var-inj (i ≟ j)
(σ ⇒ τ) ≟ᵀ (σ' ⇒ τ') = dcong₂ _⇒_ ⇒-inj (σ ≟ᵀ σ') (τ ≟ᵀ τ')
Var _   ≟ᵀ (_ ⇒ _)   = no λ()
(_ ⇒ _) ≟ᵀ Var _     = no λ()

instance
  DecEq-Type : DecEq Type
  DecEq-Type = record { _≟_ = _≟ᵀ_ }
