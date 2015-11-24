{-# OPTIONS --rewriting #-}

module STLC.Core.Properties where

open import STLC.Lib.Prelude
open import STLC.Core.Type
open import STLC.Core.Term
open Membership

Var-inj : ∀ {n} {i j : Fin n} -> Var i ≡ Var j -> i ≡ j
Var-inj refl = refl

⇒-inj : ∀ {n} {σ₁ σ₂ τ₁ τ₂ : Type n} -> σ₁ ⇒ τ₁ ≡ σ₂ ⇒ τ₂ -> σ₁ ≡ σ₂ × τ₁ ≡ τ₂
⇒-inj refl = refl , refl

▻-inj : ∀ {n σ₁ σ₂} {Γ₁ Γ₂ : Con n} -> Γ₁ ▻ σ₁ ≡ Γ₂ ▻ σ₂ -> Γ₁ ≡ Γ₂ × σ₁ ≡ σ₂
▻-inj refl = refl , refl

instance
  Type-DecEq : ∀ {n} -> DecEq (Type n)
  Type-DecEq = record { _≟_ = _≟ᵗ_ } where
    infix 4 _≟ᵗ_
    _≟ᵗ_ : ∀ {n} -> Decidable (_≡_ {A = Type n})
    Var i   ≟ᵗ Var j   = dcong Var Var-inj (i ≟ j)
    σ₁ ⇒ τ₁ ≟ᵗ σ₂ ⇒ τ₂ = dcong₂ _⇒_ ⇒-inj (σ₁ ≟ᵗ σ₂) (τ₁ ≟ᵗ τ₂)
    Var i   ≟ᵗ σ₂ ⇒ τ₂ = no λ()
    σ₁ ⇒ τ₁ ≟ᵗ Var j   = no λ()

  Con-DecEq : ∀ {n} -> DecEq (Con n)
  Con-DecEq = record { _≟_ = _≟ᶜ_ } where
    infix 4 _≟ᶜ_
    _≟ᶜ_ : ∀ {n} -> Decidable (_≡_ {A = Con n})
    ε     ≟ᶜ ε     = yes refl
    Γ ▻ σ ≟ᶜ Δ ▻ τ = dcong₂ _▻_ ▻-inj (Γ ≟ᶜ Δ) (σ ≟ τ)
    ε     ≟ᶜ Δ ▻ τ = no λ()
    Γ ▻ σ ≟ᶜ ε     = no λ()

sub-self : ∀ {n σ} -> (i : Fin n) -> [ i / σ ] i ≡ σ
sub-self i rewrite ≟-refl i = refl

non-sub : ∀ {n σ τ} {i : Fin n} -> i ∉ ftv-all σ -> apply [ i / τ ] σ ≡ σ
non-sub {σ = Var j} {i = i} c with i ≟ j
... | yes p rewrite p = ⊥-elim (c here)
... | no  d = refl
non-sub {σ = σ ⇒ τ} c = cong₂ _⇒_ (non-sub (c ∘ ∈-++₁)) (non-sub (c ∘ ∈-++₂ (ftv-all σ)))

sub : ∀ {n} i -> (τ : Type n) -> Maybe (∃ λ (Ψ : Subst n n) -> apply Ψ (Var i) ≡ apply Ψ τ)
sub i σ = drec (const nothing)
               (λ c -> just ([ i / σ ] , right (sub-self i) (non-sub c)))
               (i ∈? ftv-all σ)

apply-apply : ∀ {n m p} {Φ : Subst m p} {Ψ : Subst n m} σ
            -> apply Φ (apply Ψ σ) ≡ apply (Φ ∘ˢ Ψ) σ
apply-apply (Var i) = refl
apply-apply (σ ⇒ τ) = cong₂ _⇒_ (apply-apply σ) (apply-apply τ)

foldrᶜ-mapᶜ : ∀ {α n m} {A : Set α} {g : Type m -> A -> A} {f : Type n -> Type m} {z} Γ
            -> foldrᶜ g z (mapᶜ f Γ) ≡ foldrᶜ (g ∘ f) z Γ
foldrᶜ-mapᶜ              ε      = refl
foldrᶜ-mapᶜ {g = g} {f} (Γ ▻ σ) = cong (g (f σ)) (foldrᶜ-mapᶜ Γ)

⊂-inj : ∀ {n σ τ} {Γ Δ : Con n} -> Γ ⊂[ σ ] Δ ▻ τ -> Γ ⊂[ σ ] Δ ⊎ Γ ≡ Δ × σ ≡ τ
⊂-inj  vtop     = inj₂ (refl , refl)
⊂-inj (vskip p) = inj₁ p

-- Not nice.
_⊂?_ : ∀ {n} {σ : Type n} -> Decidable _⊂[ σ ]_
_⊂?_         Γ  ε      = no λ()
_⊂?_ {σ = σ} Γ (Δ ▻ τ) with λ c₁ -> drec (yes ∘ vskip) (λ c₂ -> no ([ c₂ , c₁ ] ∘ ⊂-inj)) (Γ ⊂? Δ)
... | r with σ ≟ τ
... | no  c₁ = r (c₁ ∘ proj₂)
... | yes p₁ rewrite p₁ with Γ ≟ Δ
... | no  c₁ = r (c₁ ∘ proj₁)
... | yes p₂ rewrite p₂ = yes vtop
