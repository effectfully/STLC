module STLC.NbE.Main where

open import STLC.Lib.Prelude
open import STLC.Core.Type
open import STLC.Core.Term
open import STLC.Core.Semantics
open import STLC.NbE.NF

infix  4 _⊨_ _⊨*_
infixl 6 _·ᵐ_

mutual
  _⊨_ : Links
  Γ ⊨ σ = Γ ⊢ⁿᵉ σ ⊎ Γ ⊨* σ

  _⊨*_ : Links
  Γ ⊨* Var i = ⊥
  Γ ⊨* σ ⇒ τ = ∀ {Δ} -> Γ ⊆ Δ -> Δ ⊨ σ -> Δ ⊨ τ

varᵐ : _∋_ ∸> _⊨_
varᵐ = inj₁ ∘ varⁿᵉ
  
open Kripkable record
  { _∙_  = _⊨_
  ; varˢ = varᵐ
  }

renᵐ : Renames _⊨_
renᵐ             ι (inj₁ n)  = inj₁ (renⁿᵉ ι n)
renᵐ {σ = Var i} ι (inj₂ ())
renᵐ {σ = σ ⇒ τ} ι (inj₂ k)  = inj₂ (renᵏ ι k)

readback : _⊨_ ∸> _⊢ⁿᶠ_
readback             (inj₁ n)  = neⁿᶠ n
readback {σ = Var i} (inj₂ ())
readback {σ = σ ⇒ τ} (inj₂ k)  = ƛⁿᶠ (readback (apᵏ k))

_·ᵐ_ : ∀ {n σ τ} {Γ : Con n} -> Γ ⊨ σ ⇒ τ -> Γ ⊨ σ -> Γ ⊨ τ
inj₁ f ·ᵐ x = inj₁ (f ·ⁿᵉ readback x)
inj₂ k ·ᵐ x = k ·ᵏ x

open Environment record
  { renˢ = renᵐ
  }

open Semantics record
  { _◆_  = _⊨_
  ; embˢ = id
  ; lamˢ = inj₂
  ; _·ˢ_ = _·ᵐ_
  }

nf : _⊢_ ∸> _⊢ⁿᶠ_
nf = readback ∘ eval

norm : _⊢_ ∸> _⊢_
norm = embⁿᶠ ∘ nf
