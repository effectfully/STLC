module HMTS.NbE.LiftableTerms where

open import Function
open import Relation.Nullary
open import Data.Maybe.Base
open import Data.List.Base hiding ([_])

open import HMTS.Utilities.Prelude
open import HMTS.Data.Type
open import HMTS.Data.Term
open import HMTS.NbE.NormalForm
open import HMTS.NbE.Environment

⊢ⁿᶠ_ : Type -> Set
⊢ⁿᶠ σ = ∀ {Γ} -> Γ ⊢ⁿᶠ σ

⊢ⁿᵉ_ : Type -> Set
⊢ⁿᵉ σ = ∀ {Γ} -> Γ ⊢ⁿᵉ σ

[_]ᵀ : Type -> Set
[ Var i ]ᵀ = ⊢ⁿᶠ Var i
[ σ ⇒ τ ]ᵀ = [ σ ]ᵀ -> [ τ ]ᵀ 

mutual
  ↑ : ∀ {σ} -> ⊢ⁿᵉ σ -> [ σ ]ᵀ
  ↑ {Var i} n = ne n
  ↑ {σ ⇒ τ} f = λ y -> ↑ (f ·ⁿᵉ ↓ y)
  
  ↓ : ∀ {σ} -> [ σ ]ᵀ -> ⊢ⁿᶠ σ
  ↓ {Var i} n     = n
  ↓ {σ ⇒ τ} f {Γ} = ƛⁿᶠ (↓ (f (↑ᵛᶻ Γ σ)))

  ↑ᵛᶻ : ∀ Γ σ -> [ σ ]ᵀ
  ↑ᵛᶻ Γ σ = ↑ (WEAKEN (Γ ▻ σ) (varⁿᵉ vz)) where
  
    WEAKEN : ∀ {Δ σ} Γ -> Γ ⊢ⁿᵉ σ -> Δ ⊢ⁿᵉ σ
    WEAKEN {Δ} Γ n = case Γ ⊆? Δ of λ
      { (yes sub) -> weakenⁿᵉ sub n
      ; (no  _  ) -> impossible
      } where postulate impossible : _

↑s : ∀ {Γ} -> Env [_]ᵀ Γ
↑s {[]}    = Ø
↑s {σ ∷ Γ} = ↑s ▷ ↑ᵛᶻ Γ σ

[_] : ∀ {Γ σ} -> Γ ⊢ σ -> Env [_]ᵀ Γ -> [ σ ]ᵀ
[ var v ] ρ = lookup v ρ
[ ƛ b   ] ρ = λ y -> [ b ] (ρ ▷ y)
[ f ∙ x ] ρ = [ f ] ρ ([ x ] ρ)

normalize : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ
normalize e = fromⁿᶠ (↓ ([ e ] ↑s))
