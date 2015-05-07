module HMTS.Alpha where

open import Level
open import Function
open import Data.Product
open import Data.List as List

open import HMTS.Prelude
open import HMTS.Types
open import HMTS.Substitutions
open import HMTS.Terms

specialize-var : ∀ {Γ σ Ψ} -> σ ∈ Γ -> apply Ψ σ ∈ List.map (apply Ψ) Γ
specialize-var  vz    = vz
specialize-var (vs v) = vs (specialize-var v)

specialize : ∀ {Γ σ Ψ} -> Γ ⊢ σ -> List.map (apply Ψ) Γ ⊢ apply Ψ σ
specialize (var v) = var (specialize-var v)
specialize (ƛ b)   = ƛ (specialize b)
specialize (f ∙ x) = specialize f ∙ specialize x

Generalize : ∀ {γ α β} {A : Set α} {B : Set β}
           -> List A -> (List (A × B) -> Set (β ⊔ γ)) -> Set (β ⊔ γ)
Generalize      []      C = C []
Generalize {γ} (x ∷ xs) C = ∀ {y} -> Generalize {γ} xs (C ∘ _∷_ (x , y))

generalize : ∀ {Γ σ} {c : Subst -> Subst} is -> Γ ⊢ σ -> Generalize is λ Ψ
           -> let Φ = c Ψ in List.map (apply Φ) Γ ⊢ apply Φ σ
generalize  []      e = specialize e
generalize (i ∷ is) e = generalize is e

alpha : ∀ {Γ σ} -> Γ ⊢ σ -> Generalize (ftv σ) λ Ψ -> List.map (apply Ψ) Γ ⊢ apply Ψ σ
alpha {σ = σ} = generalize (ftv σ)
