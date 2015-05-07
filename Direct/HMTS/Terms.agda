module HMTS.Terms where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Maybe
open import Data.Product
open import Data.List
open import Data.Vec  as Vec hiding (fromList)

open import HMTS.Prelude
open import HMTS.Types
open import HMTS.Substitutions

infix  1 _⊢_

data _⊢_ {n} (Γ : Con n) : Type -> Set where
  var : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _∙_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ

Term : Type -> Set
Term σ = [] ⊢ σ

coerceBy : ∀ {n σ τ} {Γ : Con n} -> σ ≡ τ -> Γ ⊢ σ -> Γ ⊢ τ
coerceBy refl = id

atom-specialize-var : ∀ {ψ n σ} {Γ : Con n} -> σ ∈ Γ -> atom-apply ψ σ ∈ Vec.map (atom-apply ψ) Γ
atom-specialize-var  here     = here
atom-specialize-var (there v) = there (atom-specialize-var v)

atom-specialize : ∀ {ψ n σ} {Γ : Con n} -> Γ ⊢ σ -> Vec.map (atom-apply ψ) Γ ⊢ atom-apply ψ σ
atom-specialize (var v) = var (atom-specialize-var v)
atom-specialize (ƛ b)   = ƛ (atom-specialize b)
atom-specialize (f ∙ x) = atom-specialize f ∙ atom-specialize x

specialize : ∀ {n σ} {Γ : Con n} Ψ -> Γ ⊢ σ -> map-apply Ψ Γ ⊢ apply Ψ σ
specialize (leaf   ψ)   e = atom-specialize e
specialize (branch Φ Ψ) e = specialize Φ (specialize Ψ e)
