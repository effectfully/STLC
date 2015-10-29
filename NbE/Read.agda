module STLC.NbE.Read where

open import STLC.Lib.Prelude
open import STLC.Core.Type
open import STLC.Core.Term
open import STLC.Core.Properties
open import STLC.NbE.NF

Ne : ∀ {n} -> Type n -> Set
Ne σ = ∀ {Γ} -> Γ ⊢ⁿᵉ σ

NF : ∀ {n} -> Type n -> Set
NF σ = ∀ {Γ} -> Γ ⊢ⁿᶠ σ

⟦_⟧ : ∀ {n} -> Type n -> Set
⟦ Var i ⟧ = Ne (Var i)
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ -> ⟦ τ ⟧

mutual
  ↑ : ∀ {n} {σ : Type n} -> Ne σ -> ⟦ σ ⟧
  ↑ {σ = Var i} n = n
  ↑ {σ = σ ⇒ τ} f = λ x -> ↑ (f ·ⁿᵉ ↓ x)

  ↓ : ∀ {n} {σ : Type n} -> ⟦ σ ⟧ -> NF σ
  ↓ {σ = Var i} n = neⁿᶠ n
  ↓ {σ = σ ⇒ τ} f = λ {Γ} -> ƛⁿᶠ (↓ (f (↑ (λ {Δ} -> varⁿᵉ (diff Δ Γ σ))))) where
    diff : ∀ Δ Γ σ -> σ ∈ Δ
    diff Δ Γ σ = drec ⊂[]-to-∈ impossible (Γ ⊂? Δ)  where
      postulate impossible : _

read : ∀ {n} {σ : Type n} -> ⟦ σ ⟧ -> Term σ
read x = term (embⁿᶠ (↓ x {ε}))
