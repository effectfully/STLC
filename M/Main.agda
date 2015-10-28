module STLC.M.Main where

open import STLC.Lib.Prelude
open import STLC.Core.Syntax
open import STLC.Core.Type
open import STLC.M.Term

-- `specialize' as a constructor?
M : ∀ {n l} -> (Γ : Con n l) -> Syntax l -> (σ : Type n)
  -> Maybe (∃ λ m -> ∃ λ (Ψ : Subst n m) -> mapᶜ (apply Ψ) Γ ⊢ apply Ψ σ)
M Γ (var i)   σ =
  unify σ (lookupᶜ i Γ)
    >>= λ{ (Ψ , p) ->
  just (, Ψ , coerceBy (sym p) (specialize Ψ (var (lookupᶜ-∈ i Γ))))
  }
M Γ (ƛ bˢ)    σ =
  unify (renᵗ 2 σ) (Var zero ⇒ Var (suc zero))
    >>= λ{ (Ψ , p)     ->
  M (mapᶜ (apply (Ψ ∘ raise 2)) Γ ▻ apply Ψ (Var zero)) bˢ (apply Ψ (Var (suc zero)))
    >>= λ{ (_ , Φ , b) ->
  just (, apply Φ ∘ Ψ ∘ raise 2 , coerceBy (cong (apply Φ) (sym p)) (ƛ b))
  }}
M Γ (fˢ · xˢ) σ =
  M (mapᶜ (renᵗ 1) Γ)              fˢ (Var zero ⇒ renᵗ 1 σ)
    >>= λ{ (_ , Ψ , f) ->
  M (mapᶜ (apply (Ψ ∘ raise 1)) Γ) xˢ (apply Ψ (Var zero))
    >>= λ{ (_ , Φ , x) ->
  just (, apply Φ ∘ Ψ ∘ raise 1 , specialize Φ f · x)
  }}

infer : Syntax⁽⁾ -> _
infer e = M ε e (Var {1} zero)
