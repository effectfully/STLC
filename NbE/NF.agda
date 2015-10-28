module STLC.NbE.NF where

open import STLC.Core.Type
open import STLC.Core.Term

infix  4 _⊢ⁿᵉ_ _⊢ⁿᶠ_
infixl 6 _·ⁿᵉ_

mutual
  data _⊢ⁿᵉ_ {n} Γ : Type n -> Set where
    varⁿᵉ : ∀ {σ}   -> σ ∈ Γ       -> Γ ⊢ⁿᵉ σ
    _·ⁿᵉ_ : ∀ {σ τ} -> Γ ⊢ⁿᵉ σ ⇒ τ -> Γ ⊢ⁿᶠ σ -> Γ ⊢ⁿᵉ τ

  data _⊢ⁿᶠ_ {n} Γ : Type n -> Set where
    neⁿᶠ : ∀ {σ}   -> Γ ⊢ⁿᵉ σ     -> Γ ⊢ⁿᶠ σ
    ƛⁿᶠ  : ∀ {σ τ} -> Γ ▻ σ ⊢ⁿᶠ τ -> Γ ⊢ⁿᶠ σ ⇒ τ

mutual
  embⁿᵉ : _⊢ⁿᵉ_ ∸> _⊢_
  embⁿᵉ (varⁿᵉ v) = var v
  embⁿᵉ (f ·ⁿᵉ x) = embⁿᵉ f · embⁿᶠ x

  embⁿᶠ : _⊢ⁿᶠ_ ∸> _⊢_
  embⁿᶠ (neⁿᶠ x) = embⁿᵉ x
  embⁿᶠ (ƛⁿᶠ b)  = ƛ (embⁿᶠ b)

mutual
  renⁿᵉ : Renames _⊢ⁿᵉ_
  renⁿᵉ ι (varⁿᵉ v) = varⁿᵉ (renᵛ ι v)
  renⁿᵉ ι (f ·ⁿᵉ x) = renⁿᵉ ι f ·ⁿᵉ renⁿᶠ ι x

  renⁿᶠ : Renames _⊢ⁿᶠ_
  renⁿᶠ ι (neⁿᶠ n) = neⁿᶠ (renⁿᵉ ι n)
  renⁿᶠ ι (ƛⁿᶠ  b) = ƛⁿᶠ (renⁿᶠ (keep ι) b)
