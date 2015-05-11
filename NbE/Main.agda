module HMTS.NbE.Main where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List hiding ([_])
open import Algebra

open import HMTS.Utilities.Prelude
open import HMTS.Data.Type
open import HMTS.Data.Term
open import HMTS.NbE.NormalForm
open import HMTS.NbE.Environment

open Monoid (monoid Type) hiding (_∙_; sym)

[_/_] : Con -> Type -> Set
[ Γ / Var i ] = Γ ⊢ⁿᵉ Var i
[ Γ / σ ⇒ τ ] = ∀ Δ -> [ Γ ▻▻ Δ / σ ] -> [ Γ ▻▻ Δ / τ ]

cast : ∀ {Γ Δ σ} -> Γ ≡ Δ -> [ Γ / σ ] -> [ Δ / σ ]
cast refl y = y

weakenˢᵉᵐ : ∀ {σ Γ} Δ -> [ Γ / σ ] -> [ Γ ▻▻ Δ / σ ]
weakenˢᵉᵐ {Var i} Δ n = weakenⁿᵉ (⊆-refl-++₂ Δ) n
weakenˢᵉᵐ {σ ⇒ τ} Δ f = λ Ε y ->
   cast (assoc Ε Δ _) (f (Δ ▻▻ Ε) (cast (sym (assoc Ε Δ _)) y))
  
mutual
  ↑ : ∀ {σ Γ} -> Γ ⊢ⁿᵉ σ -> [ Γ / σ ]
  ↑ {Var i} n = n
  ↑ {σ ⇒ τ} f = λ Δ y -> ↑ (weakenⁿᵉ (⊆-refl-++₂ Δ) f ·ⁿᵉ ↓ y)

  ↓ : ∀ {σ Γ} -> [ Γ / σ ] -> Γ ⊢ⁿᶠ σ
  ↓ {Var i} n = ne n
  ↓ {σ ⇒ τ} f = ƛⁿᶠ (↓ (f (ε ▻ σ) (↑ (varⁿᵉ vz))))

varˢᵉᵐ : ∀ {Γ σ} -> σ ∈ Γ -> [ Γ / σ ]
varˢᵉᵐ v = ↑ (varⁿᵉ v)

idˢᵘᵇ : ∀ {Γ} -> Γ =[ [_/_] ]> Γ
idˢᵘᵇ {[]}    = Ø
idˢᵘᵇ {σ ∷ Γ} = map-Env (weakenˢᵉᵐ ([] ▻ σ)) idˢᵘᵇ ▷ varˢᵉᵐ vz

[_] : ∀ {Γ Δ σ} -> Γ ⊢ σ -> Γ =[ [_/_] ]> Δ -> [ Δ / σ ]
[ var v ] ρ = lookup v ρ
[ ƛ b   ] ρ = λ Ε y -> [ b ] (map-Env (weakenˢᵉᵐ Ε) ρ ▷ y)
[ f ∙ x ] ρ = [ f ] ρ ε ([ x ] ρ)

normalize : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ
normalize e = fromⁿᶠ (↓ ([ e ] idˢᵘᵇ))
