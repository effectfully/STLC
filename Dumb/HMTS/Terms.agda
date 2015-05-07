module HMTS.Terms where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Maybe
open import Data.List
open import Data.Vec as Vec hiding (_>>=_; _⊛_; _∈_; module _∈_)

open import HMTS.Prelude
open import HMTS.Types
open import HMTS.Annotated

infix  1 _⊢_

_▻_ : ∀ {α} {A : Set α} -> List A -> A -> List A
_▻_ = flip _∷_

data _⊢_ (Γ : List Type) : Type -> Set where
  var : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _∙_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ

Term : Type -> Set
Term σ = [] ⊢ σ

cod : Type -> Type
cod (σ ⇒ τ) = τ
cod  σ      = σ

typeOfInᵃ : ∀ {n} -> Con n -> Annotated n -> Type
typeOfInᵃ Γ (varᵃ i) = Vec.lookup i Γ
typeOfInᵃ Γ (ƛᵃ σ b) = σ ⇒ typeOfInᵃ (σ ∷ Γ) b
typeOfInᵃ Γ (f ·ᵃ x) = cod (typeOfInᵃ Γ f)

coerce : ∀ {Γ σ τ} -> Γ ⊢ σ -> Maybe (Γ ⊢ τ)
coerce {Γ} {σ} {τ} e = (λ p -> subst (_⊢_ Γ) p e) <$> (σ ≟ᵀ τ)

typifyInᵃ : ∀ {n} -> (Γ : Vec Type n) -> (e : Annotated n) -> Maybe (toList Γ ⊢ typeOfInᵃ Γ e) 
typifyInᵃ Γ (varᵃ i)   = just (var (lookup-in i Γ))
typifyInᵃ Γ (ƛᵃ σ bᵃ)  = ƛ_ <$> typifyInᵃ (σ ∷ Γ) bᵃ
typifyInᵃ Γ (fᵃ ·ᵃ xᵃ) with typeOfInᵃ Γ fᵃ | typifyInᵃ Γ fᵃ | typifyInᵃ Γ xᵃ
... | σ ⇒ τ | f | x = _∙_ <$> f ⊛ (x >>= coerce)
... | _      | _ | _ = nothing 

typeOfᵃ : Annotated⁽⁾ -> Type
typeOfᵃ = typeOfInᵃ []

typifyᵃ : ∀ e -> Maybe (Term (typeOfᵃ e))
typifyᵃ = typifyInᵃ []
