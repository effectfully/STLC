module STLC.Data.Term where

open import Data.List.Base as List
open import Data.Vec hiding (_∈_)

open import STLC.Utilities.Prelude
open import STLC.Data.Syntax
open import STLC.Data.Type
open import STLC.AlgorithmM.Substitution
open import STLC.AlgorithmM.Term renaming (_⊢_ to _⊢ᵛ_; module _⊢_ to _⊢ᵛ_) hiding (erase)

infix  1 _⊢_
infixl 5 _∙_

data _⊢_ (Γ : Con) : Type -> Set where
  var : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _∙_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ

Term : Type -> Set
Term σ = [] ⊢ σ

erase : ∀ {Γ σ} -> Γ ⊢ σ -> Syntax (length Γ)
erase (var v) = varˢ (∈-to-Fin v)
erase (ƛ b)   = ƛˢ (erase b)
erase (f ∙ x) = erase f · erase x

unʳ : ∀ {n σ} {Γ : Conᵛ n} -> Γ ⊢ʳ σ -> toList Γ ⊢ σ
unʳ (var v) = var (∈ᵛ-to-∈ v)
unʳ (ƛ b)   = ƛ (unʳ b)
unʳ (f ∙ x) = unʳ f ∙ unʳ x
