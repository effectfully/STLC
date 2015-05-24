module STLC.Utilities.Generalize where

open import Level
open import Function
open import Relation.Nullary.Decidable
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Maybe.Base
open import Data.Product   as Prod
open import Data.List.Base as List

open import STLC.Utilities.Prelude
open import STLC.Data.Type
open import STLC.Data.Term

Subst : Set
Subst = List (ℕ × Type)

apply : Subst -> Type -> Type
apply Ψ (Var i) = maybe′ id (Var i) (lookup-for i Ψ)
apply Ψ (σ ⇒ τ) = apply Ψ σ ⇒ apply Ψ τ

specialize-var : ∀ {Γ σ Ψ} -> σ ∈ Γ -> apply Ψ σ ∈ List.map (apply Ψ) Γ
specialize-var  vz    = vz
specialize-var (vs v) = vs (specialize-var v)

specialize : ∀ {Ψ Γ σ} -> Γ ⊢ σ -> List.map (apply Ψ) Γ ⊢ apply Ψ σ
specialize (var v) = var (specialize-var v)
specialize (ƛ b)   = ƛ (specialize b)
specialize (f ∙ x) = specialize f ∙ specialize x

generalizeᶜ : ∀ {Γ σ} {c : Subst -> Subst} is
            -> Γ ⊢ σ -> Associate is λ Ψ -> let Φ = c Ψ in List.map (apply Φ) Γ ⊢ apply Φ σ
generalizeᶜ  []      e = specialize e
generalizeᶜ (i ∷ is) e = generalizeᶜ is e

generalize : ∀ {σ Γ} -> Γ ⊢ σ -> Associate (ftv σ) λ Ψ -> List.map (apply Ψ) Γ ⊢ apply Ψ σ
generalize {σ} = generalizeᶜ (ftv σ)

thicken : ∀ {σ Γ} -> Γ ⊢ σ -> _
thicken {σ} = specialize {List.map (λ{ (i , j) -> (j , Var i) }) (enumerate (ftv σ))}

private
  K : Term (Var 0 ⇒ Var 1 ⇒ Var 0)
  K = ƛ ƛ var (vs vz)

  K' : Term (Var 2 ⇒ Var 0 ⇒ Var 2)
  K' = generalize K

  K'' : ∀ {a b} -> Term (a ⇒ b ⇒ a)
  K'' = generalize K
