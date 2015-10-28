module STLC.Core.Semantics where

open import STLC.Lib.Prelude
open import STLC.Core.Type
open import STLC.Core.Term

-- Forgive me this.
record Kripkable : Set₁ where
  infix  4 _∙_
  infixr 9 _∘ᵏ_

  field
    _∙_  : Links
    varˢ : _∋_ ∸> _∙_

  Kripke : ∀ {n} -> Con n -> Type n -> Type n -> Set
  Kripke Γ σ τ = ∀ {Δ} -> Γ ⊆ Δ -> Δ ∙ σ -> Δ ∙ τ

  apᵏ : ∀ {n σ τ} {Γ : Con n} -> Kripke Γ σ τ -> Γ ▻ σ ∙ τ
  apᵏ k = k top (varˢ vz)

  _·ᵏ_ : ∀ {n σ τ} {Γ : Con n} -> Kripke Γ σ τ -> Γ ∙ σ -> Γ ∙ τ
  k ·ᵏ t = k stop t

  renᵏ : ∀ {n σ τ} {Γ Δ : Con n} -> Γ ⊆ Δ -> Kripke Γ σ τ -> Kripke Δ σ τ
  renᵏ ι k κ = k (κ ∘ˢ ι)

  _∘ᵏ_ : ∀ {n σ τ ν} {Γ : Con n} -> Kripke Γ τ ν -> Kripke Γ σ τ -> Kripke Γ σ ν
  (k₂ ∘ᵏ k₁) ι = k₂ ι ∘ k₁ ι

  record Environment : Set where
    infix 4 _⊢*_

    field
      renˢ : Renames _∙_

    data _⊢*_ {n} Δ : Con n -> Set where
      Ø   : Δ ⊢* ε
      _▷_ : ∀ {Γ σ} -> Δ ⊢* Γ -> Δ ∙ σ -> Δ ⊢* Γ ▻ σ

    lookupᵉ : ∀ {n σ} {Γ Δ : Con n} -> σ ∈ Γ -> Δ ⊢* Γ -> Δ ∙ σ
    lookupᵉ  vz    (ρ ▷ x) = x
    lookupᵉ (vs v) (ρ ▷ x) = lookupᵉ v ρ

    renᵉ : ∀ {n} {Γ Δ Ξ : Con n} -> Δ ⊆ Ξ -> Δ ⊢* Γ -> Ξ ⊢* Γ
    renᵉ ι  Ø      = Ø
    renᵉ ι (ρ ▷ x) = renᵉ ι ρ ▷ renˢ ι x

    keepᵉ : ∀ {n σ} {Γ Δ : Con n} -> Δ ⊢* Γ -> Δ ▻ σ ⊢* Γ ▻ σ
    keepᵉ ρ = renᵉ top ρ ▷ varˢ vz

    idᵉ : ∀ {n} {Γ : Con n} -> Γ ⊢* Γ
    idᵉ {Γ = ε}     = Ø
    idᵉ {Γ = Γ ▻ σ} = keepᵉ idᵉ

    record Semantics : Set₁ where
      infix  4 _◆_
      infixl 6 _·ˢ_

      field
        _◆_  : Links
        embˢ : _∙_ ∸> _◆_
        lamˢ : ∀ {n σ τ} {Γ : Con n} -> (∀ {Δ} -> Γ ⊆ Δ -> Δ ∙ σ -> Δ ◆ τ) -> Γ ◆ σ ⇒ τ
        _·ˢ_ : ∀ {n σ τ} {Γ : Con n} -> Γ ◆ σ ⇒ τ -> Γ ◆ σ -> Γ ◆ τ

      ⟦_⟧ : ∀ {n σ} {Δ Γ : Con n} -> Γ ⊢ σ -> Δ ⊢* Γ -> Δ ◆ σ
      ⟦ var v ⟧ ρ = embˢ (lookupᵉ v ρ)
      ⟦ ƛ b   ⟧ ρ = lamˢ λ ι x -> ⟦ b ⟧ (renᵉ ι ρ ▷ x)
      ⟦ f · x ⟧ ρ = ⟦ f ⟧ ρ ·ˢ ⟦ x ⟧ ρ

      eval : _⊢_ ∸> _◆_
      eval t = ⟦ t ⟧ idᵉ
