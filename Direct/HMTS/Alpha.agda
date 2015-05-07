module HMTS.Alpha where

open import Level
open import Function
open import Relation.Nullary.Decidable
open import Data.Bool
open import Data.Nat  as Nat
open import Data.Maybe
open import Data.Product
open import Data.List as List
open import Data.Vec  as Vec hiding (lookup)

open import HMTS.Prelude
open import HMTS.Types
open import HMTS.Terms using (_⊢_; var; ƛ_; _∙_)

Subst : Set
Subst = List (ℕ × Type)

apply : Subst -> Type -> Type
apply Ψ (Var i) = maybe′ id (Var i) (lookup i Ψ)
apply Ψ (σ ⇒ τ) = apply Ψ σ ⇒ apply Ψ τ

specialize-var : ∀ {n σ Ψ} {Γ : Con n} -> σ ∈ Γ -> apply Ψ σ ∈ Vec.map (apply Ψ) Γ
specialize-var  here     = here
specialize-var (there v) = there (specialize-var v)

specialize : ∀ {n σ Ψ} {Γ : Con n} -> Γ ⊢ σ -> Vec.map (apply Ψ) Γ ⊢ apply Ψ σ
specialize (var v) = var (specialize-var v)
specialize (ƛ b)   = ƛ (specialize b)
specialize (f ∙ x) = specialize f ∙ specialize x

Generalize : ∀ {γ α β} {A : Set α} {B : Set β}
           -> List A -> (List (A × B) -> Set (β Level.⊔ γ)) -> Set (β Level.⊔ γ)
Generalize      []      C = C []
Generalize {γ} (x ∷ xs) C = ∀ {y} -> Generalize {γ} xs (C ∘ _∷_ (x , y))

generalize : ∀ {n σ} {Γ : Con n} {c : Subst -> Subst} is
           -> Γ ⊢ σ -> Generalize is λ Ψ -> let Φ = c Ψ in Vec.map (apply Φ) Γ ⊢ apply Φ σ
generalize  []      e = specialize e
generalize (i ∷ is) e = generalize is e

alpha : ∀ {n σ} {Γ : Con n}
      -> Γ ⊢ σ -> Generalize (ftv σ) λ Ψ -> Vec.map (apply Ψ) Γ ⊢ apply Ψ σ
alpha {σ = σ} = generalize (ftv σ)
