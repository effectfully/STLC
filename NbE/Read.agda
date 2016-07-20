module STLC.NbE.Read where

open import STLC.Lib.Prelude
open import STLC.Term
open import STLC.NbE.NF

Ne : ∀ {n} -> Type n -> Set
Ne σ = Wrap (∀ {Γ} -> Γ ⊢ⁿᵉ σ)

NF : ∀ {n} -> Type n -> Set
NF σ = ∀ {Γ} -> Γ ⊢ⁿᶠ σ

⟦_⟧ : ∀ {n} -> Type n -> Set
⟦ Var i ⟧ = Ne (Var i)
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ -> ⟦ τ ⟧

mutual
  ↑ : ∀ {n} {σ : Type n} -> Ne σ -> ⟦ σ ⟧
  ↑ {σ = Var i} n = n
  ↑ {σ = σ ⇒ τ} f = λ x -> ↑ (wrap (unwrap f ·ⁿᵉ ↓ x))

  ↓ : ∀ {n} {σ : Type n} -> ⟦ σ ⟧ -> NF σ
  ↓ {σ = Var i} n     = neⁿᶠ (unwrap n)
  ↓ {σ = σ ⇒ τ} f {Γ} = ƛⁿᶠ (↓ (f (↑ (wrap λ {Δ} -> varⁿᵉ (diff Δ Γ σ))))) where
    diff : ∀ Δ Γ σ -> σ ∈ Δ
    diff Δ Γ σ = drec ⊂[]-to-∈ impossible (Γ ⊂? Δ) where
      postulate impossible : _

read : ∀ {n} {σ : Type n} -> ⟦ σ ⟧ -> Term σ
read x = wk (embⁿᶠ (↓ x {ε}))

inst : ∀ n {F : N-ary n Set Set} -> ∀ⁿ n F -> F $ᵗⁿ tabulate {n} (Ne ∘ Var)
inst n f = f $ⁿ tabulate {n} (Ne ∘ Var)

instʰ : ∀ n {F : N-ary n Set Set} -> ∀ⁿʰ n F -> F $ᵗⁿ tabulate {n} (Ne ∘ Var)
instʰ n y = y $ⁿʰ tabulate {n} (Ne ∘ Var)
