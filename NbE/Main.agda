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

[_/_]ᵀ : Con -> Type -> Set
[ Γ / Var i ]ᵀ = Γ ⊢ⁿᵉ Var i
[ Γ / σ ⇒ τ ]ᵀ = ∀ Δ -> [ Γ ▻▻ Δ / σ ]ᵀ -> [ Γ ▻▻ Δ / τ ]ᵀ

cast : ∀ {Γ Δ σ} -> Γ ≡ Δ -> [ Γ / σ ]ᵀ -> [ Δ / σ ]ᵀ
cast refl y = y

weakenˢᵉᵐ : ∀ {σ Γ} Δ -> [ Γ / σ ]ᵀ -> [ Γ ▻▻ Δ / σ ]ᵀ
weakenˢᵉᵐ {Var i} Δ n = weakenⁿᵉ (⊆-refl-++₂ Δ) n
weakenˢᵉᵐ {σ ⇒ τ} Δ f = λ Ε y ->
   cast (assoc Ε Δ _) (f (Δ ▻▻ Ε) (cast (sym (assoc Ε Δ _)) y))
  
mutual
  ↑ : ∀ {σ Γ} -> Γ ⊢ⁿᵉ σ -> [ Γ / σ ]ᵀ
  ↑ {Var i} n = n
  ↑ {σ ⇒ τ} f = λ Δ y -> ↑ (weakenⁿᵉ (⊆-refl-++₂ Δ) f ·ⁿᵉ ↓ y)

  ↓ : ∀ {σ Γ} -> [ Γ / σ ]ᵀ -> Γ ⊢ⁿᶠ σ
  ↓ {Var i} n = ne n
  ↓ {σ ⇒ τ} f = ƛⁿᶠ (↓ (f (ε ▻ σ) (↑ (varⁿᵉ vz))))

varˢᵉᵐ : ∀ {Γ σ} -> σ ∈ Γ -> [ Γ / σ ]ᵀ
varˢᵉᵐ v = ↑ (varⁿᵉ v)

↑s : ∀ {Γ} -> Env ([_/_]ᵀ Γ) Γ
↑s {[]}    = Ø
↑s {σ ∷ Γ} = map-Env (weakenˢᵉᵐ ([] ▻ σ)) ↑s ▷ varˢᵉᵐ vz

[_] : ∀ {Γ Δ σ} -> Γ ⊢ σ -> Env ([_/_]ᵀ Δ) Γ -> [ Δ / σ ]ᵀ
[ var v ] ρ = lookup v ρ
[ ƛ b   ] ρ = λ Ε y -> [ b ] (map-Env (weakenˢᵉᵐ Ε) ρ ▷ y)
[ f ∙ x ] ρ = [ f ] ρ ε ([ x ] ρ)

normalize : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ
normalize e = fromⁿᶠ (↓ ([ e ] ↑s))
