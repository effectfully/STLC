module STLC.AlgorithmM.Term where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Maybe.Base
open import Data.Product
open import Data.List.Base
open import Data.Vec as Vec

open import STLC.Utilities.Prelude
open import STLC.Data.Syntax
open import STLC.Data.Type
open import STLC.AlgorithmM.Substitution

infix  1 _⊢_
infixl 5 _∙_

data _⊢_ {n} (Γ : Conᵛ n) : Type -> Set where
  var : ∀ {σ}   -> σ ∈ᵛ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ᵛ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _∙_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ  -> Γ ⊢ σ     -> Γ ⊢ τ

erase : ∀ {n σ} {Γ : Conᵛ n} -> Γ ⊢ σ -> Syntax n
erase (var v) = varˢ (∈ᵛ-to-Fin v)
erase (ƛ b)   = ƛˢ (erase b)
erase (f ∙ x) = erase f · erase x

coerceBy : ∀ {n σ τ} {Γ : Conᵛ n} -> σ ≡ τ -> Γ ⊢ σ -> Γ ⊢ τ
coerceBy refl = id

atom-specialize-var : ∀ {ψ n σ} {Γ : Conᵛ n}
                    -> σ ∈ᵛ Γ -> atom-apply ψ σ ∈ᵛ Vec.map (atom-apply ψ) Γ
atom-specialize-var  vz    = vz
atom-specialize-var (vs v) = vs (atom-specialize-var v)

atom-specialize : ∀ {ψ n σ} {Γ : Conᵛ n}
                -> Γ ⊢ σ -> Vec.map (atom-apply ψ) Γ ⊢ atom-apply ψ σ
atom-specialize (var v) = var (atom-specialize-var v)
atom-specialize (ƛ b)   = ƛ (atom-specialize b)
atom-specialize (f ∙ x) = atom-specialize f ∙ atom-specialize x

specialize : ∀ {n σ} {Γ : Conᵛ n} Ψ -> Γ ⊢ σ -> map-apply Ψ Γ ⊢ apply Ψ σ
specialize (leaf   ψ)   e = atom-specialize e
specialize (branch Φ Ψ) e = specialize Φ (specialize Ψ e)
