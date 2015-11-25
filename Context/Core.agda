module STLC.Context.Core where

open import STLC.Lib.Prelude
open import STLC.Type

infixl 5 _▻_ _▻▻_
infix  4 _⊂[_]_ _⊆_

data Con n : Set where
  ε   : Con n
  _▻_ : Con n -> Type n -> Con n

data _⊂[_]_ {n} Γ σ : Con n -> Set where
  vtop  :            Γ ⊂[ σ ] Γ ▻ σ
  vskip : ∀ {Δ τ} -> Γ ⊂[ σ ] Δ     -> Γ ⊂[ σ ] Δ ▻ τ

data _⊆_ {n} : Con n -> Con n -> Set where
  stop : ∀ {Γ}     -> Γ ⊆ Γ
  skip : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ     ⊆ Δ ▻ σ
  keep : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ▻ σ ⊆ Δ ▻ σ

Links : Set₁
Links = ∀ {n} -> Con n -> Type n -> Set

Renames : Links -> Set
Renames _∙_ = ∀ {n σ} {Γ Δ : Con n} -> Γ ⊆ Δ -> Γ ∙ σ -> Δ ∙ σ

_∸>_ : Links -> Links -> Set
_∙_ ∸> _◆_ = ∀ {n σ} {Γ : Con n} -> Γ ∙ σ -> Γ ◆ σ

foldrᶜ : ∀ {α n} {A : Set α} -> (Type n -> A -> A) -> A -> Con n -> A
foldrᶜ f z  ε      = z
foldrᶜ f z (Γ ▻ σ) = f σ (foldrᶜ f z Γ)

mapᶜ : ∀ {n m} -> (Type n -> Type m) -> Con n -> Con m
mapᶜ f = foldrᶜ (λ σ Γ -> Γ ▻ f σ) ε

lenᶜ : ∀ {n} -> Con n -> ℕ
lenᶜ = foldrᶜ (const suc) 0

_▻▻_ : ∀ {n} -> Con n -> Con n -> Con n
_▻▻_ = foldrᶜ (flip _▻_)

top : ∀ {n σ} {Γ : Con n} -> Γ ⊆ Γ ▻ σ
top = skip stop

full : ∀ {n} {Γ : Con n} -> ε ⊆ Γ
full {Γ = ε}     = stop
full {Γ = Γ ▻ σ} = skip full

_∘ᵉ_ : ∀ {n} {Γ Δ Ξ : Con n} -> Δ ⊆ Ξ -> Γ ⊆ Δ -> Γ ⊆ Ξ
stop   ∘ᵉ ι      = ι
skip κ ∘ᵉ ι      = skip (κ ∘ᵉ ι)
keep κ ∘ᵉ stop   = keep κ
keep κ ∘ᵉ skip ι = skip (κ ∘ᵉ ι)
keep κ ∘ᵉ keep ι = keep (κ ∘ᵉ ι)
