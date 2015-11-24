module STLC.M.Typecheck where

open import STLC.Lib.Prelude
open import STLC.Core.Syntax
open import STLC.Core.Type
open import STLC.Core.Unify
open import STLC.M.Term

M : ∀ {n l} -> (Γ : Con n l) -> Syntax l -> (σ : Type n) -> Maybe (∃ λ m -> Subst n m)
M Γ (var i)   σ =
  unify σ (lookupᶜ i Γ)
    >>= uncurry λ Ψ p ->
  just (, Ψ)
M Γ (ƛ bˢ)    σ =
  unify (renᵗ 2 σ) (Var zero ⇒ Var (suc zero))
    >>= uncurry λ Ψ p ->
  M (mapᶜ (apply (Ψ ∘ raise 2)) Γ ▻ apply Ψ (Var zero)) bˢ (apply Ψ (Var (suc zero)))
    >>= proj₂ >>> λ Φ ->
  just (, Φ ∘ˢ Ψ ∘ raise 2)
M Γ (fˢ · xˢ) σ =
  M (mapᶜ (renᵗ 1) Γ)              fˢ (Var zero ⇒ renᵗ 1 σ)
    >>= proj₂ >>> λ Ψ ->
  M (mapᶜ (apply (Ψ ∘ raise 1)) Γ) xˢ (apply Ψ (Var zero))
    >>= proj₂ >>> λ Φ ->
  just (, Φ ∘ˢ Ψ ∘ raise 1)

runM : Syntax⁽⁾ -> _
runM e = M ε e (Var {1} zero)

mutual
  infer : ∀ {n l} -> (Γ : Con n l) -> Syntax l -> Maybe (∃ (Γ ⊢_))
  infer Γ (var v) = just (, var (lookupᶜ-∈ v Γ))
  infer Γ (ƛ b)   = nothing
  infer Γ (f · x) = infer Γ f >>= λ
    { (σ ⇒ τ , f') -> (λ x' -> , f' · x') <$> check Γ x σ
    ; (Var i , x') -> nothing
    }

  check : ∀ {n l} -> (Γ : Con n l) -> Syntax l -> (σ : Type n) -> Maybe (Γ ⊢ σ)
  check Γ (ƛ b) (σ ⇒ τ) = ƛ_ <$> check (Γ ▻ σ) b τ
  check Γ  e     σ      = infer Γ e >>= coerce ∘ proj₂

typecheck : ∀ {n} -> Syntax⁽⁾ -> (σ : Type n) -> Maybe (ε ⊢ σ)
typecheck = check ε
