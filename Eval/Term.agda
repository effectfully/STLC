module STLC.Eval.Term where

open import Data.List.Base

open import STLC.Utilities.Prelude
open import STLC.Eval.Type

infix  1 _⊢_
infixl 5 _∙_

data _⊢_ {n} (Γ : Con n) : Type n -> Set where
  var : ∀ {σ  } -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _∙_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ

Term : ∀ {n} -> Type n -> Set
Term σ = [] ⊢ σ
