module HMTS.NbE.NormalForm where

open import HMTS.Utilities.Prelude
open import HMTS.Data.Type
open import HMTS.Data.Term

infix  1 _⊢ⁿᵉ_ _⊢ⁿᶠ_

mutual
  data _⊢ⁿᵉ_ Γ : Type -> Set where
    varⁿᵉ : ∀ {σ}   -> σ ∈ Γ      -> Γ ⊢ⁿᵉ σ
    _·ⁿᵉ_ : ∀ {σ τ} -> Γ ⊢ⁿᵉ σ ⇒ τ -> Γ ⊢ⁿᶠ σ -> Γ ⊢ⁿᵉ τ

  data _⊢ⁿᶠ_ Γ : Type -> Set where
    ne   : ∀ {σ}   -> Γ ⊢ⁿᵉ σ     -> Γ ⊢ⁿᶠ σ
    ƛⁿᶠ_ : ∀ {σ τ} -> Γ ▻ σ ⊢ⁿᶠ τ -> Γ ⊢ⁿᶠ σ ⇒ τ

mutual
  fromⁿᵉ : ∀ {Γ σ} -> Γ ⊢ⁿᵉ σ -> Γ ⊢ σ
  fromⁿᵉ (varⁿᵉ v) = var v
  fromⁿᵉ (f ·ⁿᵉ x) = fromⁿᵉ f ∙ fromⁿᶠ x

  fromⁿᶠ : ∀ {Γ σ} -> Γ ⊢ⁿᶠ σ -> Γ ⊢ σ
  fromⁿᶠ (ne n)  = fromⁿᵉ n
  fromⁿᶠ (ƛⁿᶠ b) = ƛ (fromⁿᶠ b)

mutual
  weakenⁿᵉ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ⁿᵉ σ -> Δ ⊢ⁿᵉ σ
  weakenⁿᵉ sub (varⁿᵉ v) = varⁿᵉ (sub v)
  weakenⁿᵉ sub (f ·ⁿᵉ x) = weakenⁿᵉ sub f ·ⁿᵉ weakenⁿᶠ sub x

  weakenⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ⁿᶠ σ -> Δ ⊢ⁿᶠ σ
  weakenⁿᶠ sub (ne n)  = ne (weakenⁿᵉ sub n)
  weakenⁿᶠ sub (ƛⁿᶠ b) = ƛⁿᶠ (weakenⁿᶠ (⊆-∷ sub) b)
