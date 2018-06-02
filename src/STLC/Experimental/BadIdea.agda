module STLC.Experimental.BadIdea where

open import STLC.Lib.Prelude
open import STLC.Context
open import STLC.Term

data SubstsIn {n} : Con n -> ℕ -> Set where
  øˢ   : ∀ {m} -> SubstsIn ε m
  _▷ˢ_ : ∀ {m Γ σ} -> SubstsIn Γ m -> SubstIn σ m -> SubstsIn (Γ ▻ σ) m

runSubstsIn : ∀ {n m} {Γ : Con n} -> SubstsIn Γ m -> Con m
runSubstsIn  øˢ      = ε
runSubstsIn (ρ ▷ˢ Ψ) = runSubstsIn ρ ▻ runSubstIn Ψ

-- Yeah.
specialize⁽⁾ : ∀ {n m σ} {Γ : Con n}
             -> (ρ : SubstsIn Γ m) -> (Ψ : SubstIn σ m) -> Γ ⊢ σ -> runSubstsIn ρ ⊢ runSubstIn Ψ
specialize⁽⁾ ρ Ψ (var v) = {!!}
specialize⁽⁾ ρ Ψ (ƛ b)   = ƛ (specialize⁽⁾ (ρ ▷ˢ (Ψ ∘ vl)) (Ψ ∘ vr) b)
specialize⁽⁾ ρ Ψ (f · x) = specialize⁽⁾ ρ {!!} f · specialize⁽⁾ ρ {!!} x
