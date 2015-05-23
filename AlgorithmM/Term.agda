module STLC.AlgorithmM.Term where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Maybe.Base
open import Data.Product
open import Data.Vec as Vec

open import STLC.Utilities.Prelude
open import STLC.Data.Syntax
open import STLC.Data.Type
open import STLC.AlgorithmM.Substitution

infix  3 _⊢_ _⊢ʳ_
infixl 5 _∙_

data _⊢_ {n} : Conᵛ n -> Type -> Set where
  var : ∀ {Γ σ}   -> σ ∈ᵛ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {Γ σ τ} -> Γ ▻ᵛ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _∙_ : ∀ {Γ σ τ} -> Γ ⊢ σ ⇒ τ  -> Γ ⊢ σ     -> Γ ⊢ τ
  _#_ : ∀ {Γ σ} Ψ -> Γ ⊢ σ      -> map-apply Ψ Γ ⊢ apply Ψ σ

erase : ∀ {n σ} {Γ : Conᵛ n} -> Γ ⊢ σ -> Syntax n
erase (var v) = varˢ (∈ᵛ-to-Fin v)
erase (ƛ b)   = ƛˢ (erase b)
erase (f ∙ x) = erase f · erase x
erase (Ψ # x) = erase x

coerceBy : ∀ {n σ τ} {Γ : Conᵛ n} -> σ ≡ τ -> Γ ⊢ σ -> Γ ⊢ τ
coerceBy refl = id

data _⊢ʳ_ {n} : Conᵛ n -> Type -> Set where
  var : ∀ {Γ σ}   -> σ ∈ᵛ Γ      -> Γ ⊢ʳ σ
  ƛ_  : ∀ {Γ σ τ} -> Γ ▻ᵛ σ ⊢ʳ τ -> Γ ⊢ʳ σ ⇒ τ
  _∙_ : ∀ {Γ σ τ} -> Γ ⊢ʳ σ ⇒ τ  -> Γ ⊢ʳ σ     -> Γ ⊢ʳ τ

coerceVarConByʳ : ∀ {n σ} {Γ Δ : Conᵛ n} -> Γ ≡ Δ -> σ ∈ᵛ Γ -> σ ∈ᵛ Δ
coerceVarConByʳ refl = id

coerceByʳ : ∀ {n σ τ} {Γ : Conᵛ n} -> σ ≡ τ -> Γ ⊢ʳ σ -> Γ ⊢ʳ τ
coerceByʳ refl = id

coerceConByʳ : ∀ {n σ} {Γ Δ : Conᵛ n} -> Γ ≡ Δ -> Γ ⊢ʳ σ -> Δ ⊢ʳ σ
coerceConByʳ refl = id

specialize-var : ∀ {n σ} {Γ : Conᵛ n} Ψ -> σ ∈ᵛ Γ -> apply Ψ σ ∈ᵛ map-apply Ψ Γ
specialize-var Ψ  vz    = coerceVarConByʳ (sym (▻ᵛ-expand Ψ _ _))  vz
specialize-var Ψ (vs v) = coerceVarConByʳ (sym (▻ᵛ-expand Ψ _ _)) (vs specialize-var Ψ v)

runSub : ∀ {n σ} {Γ : Conᵛ n} Ψ -> Γ ⊢ σ -> map-apply Ψ Γ ⊢ʳ apply Ψ σ
runSub Ψ (var v) = var (specialize-var Ψ v)
runSub Ψ (ƛ b)   = coerceByʳ (sym (⇒-expand Ψ _ _))
                             (ƛ (coerceConByʳ (▻ᵛ-expand Ψ _ _) (runSub Ψ b)))
runSub Ψ (f ∙ x) = coerceByʳ (⇒-expand Ψ _ _) (runSub Ψ f) ∙ runSub Ψ x
runSub Φ (Ψ # x) = runSub (branch Φ Ψ) x

unᵛ : ∀ {n σ} {Γ : Conᵛ n} -> Γ ⊢ σ -> _
unᵛ = runSub (leaf nothing)
