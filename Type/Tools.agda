module STLC.Type.Tools where

open import STLC.Lib.Prelude
open import STLC.Type.Core
open import STLC.Type.Properties

module _ where
  private postulate undefined : ∀ {α} {A : Set α} -> A

  unsafeToSubst : ∀ {n m} {σ : Type n} -> SubstIn σ m -> Subst n m
  unsafeToSubst {σ = σ} Ψ = λ i -> drec Ψ undefined (i ∈ᵗ? σ)

  thickenˢ : ∀ {n} -> (σ : Type n) -> Subst n (length (ftv σ))
  thickenˢ σ = λ i -> maybe Var undefined (thickenⱽ i σ)

-- thickenˢ : ∀ {n} -> (σ : Type n) -> SubstIn σ (length (ftv σ))
-- thickenˢ σ = λ {i} v -> inspectMaybe (thickenⱽ i σ) (λ i _ -> Var i) (⊥-elim ∘ thickenⱽ≢nothing v)
