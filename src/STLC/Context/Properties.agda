module STLC.Context.Properties where

open import STLC.Lib.Prelude
open import STLC.Type
open import STLC.Context.Core

▻-inj : ∀ {n σ₁ σ₂} {Γ₁ Γ₂ : Con n} -> Γ₁ ▻ σ₁ ≡ Γ₂ ▻ σ₂ -> Γ₁ ≡ Γ₂ × σ₁ ≡ σ₂
▻-inj refl = refl , refl

instance
  Con-DecEq : ∀ {n} -> DecEq (Con n)
  Con-DecEq = record { _≟_ = _≟ᶜ_ } where
    infix 4 _≟ᶜ_
    _≟ᶜ_ : ∀ {n} -> Decidable (_≡_ {A = Con n})
    ε     ≟ᶜ ε     = yes refl
    Γ ▻ σ ≟ᶜ Δ ▻ τ = dcong₂ _▻_ ▻-inj (Γ ≟ᶜ Δ) (σ ≟ τ)
    ε     ≟ᶜ Δ ▻ τ = no λ()
    Γ ▻ σ ≟ᶜ ε     = no λ()

foldrᶜ-mapᶜ : ∀ {α n m} {A : Set α} {g : Type m -> A -> A} {f : Type n -> Type m} {z} Γ
            -> foldrᶜ g z (mapᶜ f Γ) ≡ foldrᶜ (g ∘ f) z Γ
foldrᶜ-mapᶜ              ε      = refl
foldrᶜ-mapᶜ {g = g} {f} (Γ ▻ σ) = cong (g (f σ)) (foldrᶜ-mapᶜ Γ)

⊂-▻ : ∀ {n σ τ} {Γ Δ : Con n} -> Γ ⊂[ σ ] Δ ▻ τ -> Γ ⊂[ σ ] Δ ⊎ Γ ≡ Δ × σ ≡ τ
⊂-▻  vtop     = inj₂ (refl , refl)
⊂-▻ (vskip p) = inj₁ p

_⊂?_ : ∀ {n} {σ : Type n} -> Decidable _⊂[ σ ]_
_⊂?_         Γ  ε      = no λ()
_⊂?_ {σ = σ} Γ (Δ ▻ τ) =
  ddprod (yes % ∘ vtop′) (λ c -> r (c ∘ proj₂)) (λ c -> r (c ∘ proj₁)) (σ ≟ τ) (Γ ≟ Δ) where
    r = λ c₁ -> drec (yes ∘ vskip) (λ c₂ -> no ([ c₂ , c₁ ] ∘ ⊂-▻)) (Γ ⊂? Δ)
    
    vtop′ : ∀ {n σ τ} {Γ Δ : Con n} -> σ ≡ τ -> Γ ≡ Δ -> Γ ⊂[ σ ] Δ ▻ τ
    vtop′ refl refl = vtop
