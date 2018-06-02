{-# OPTIONS --rewriting #-}

module STLC.Type.Unify where

open import STLC.Lib.Prelude
open import STLC.Type.Core
open import STLC.Type.Properties

{-# REWRITE apply-apply #-}

{-# TERMINATING #-}
unify : ∀ {n} -> (σ τ : Type n) -> Maybe (∃ λ (Ψ : Subst n n) -> apply Ψ σ ≡ apply Ψ τ)
unify (Var i)   (Var j)   = drec (λ p -> just (Var , cong Var p)) (const (sub i (Var j))) (i ≟ j)
unify (Var i)    τ        = sub i τ
unify  σ        (Var j)   = second sym <$> sub j σ
unify (σ₁ ⇒ τ₁) (σ₂ ⇒ τ₂) =
  unify  σ₁           σ₂          >>= uncurry λ Ψ p ->
  unify (apply Ψ τ₁) (apply Ψ τ₂) >>= uncurry λ Φ q ->
  just (Φ ∘ˢ Ψ , cong₂ _⇒_ (cong (apply Φ) p) q)
