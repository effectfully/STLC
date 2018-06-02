module STLC.Type.Properties where

open import STLC.Lib.Prelude
open import STLC.Lib.Membership
open import STLC.Type.Core

Var-inj : ∀ {n} {i j : Fin n} -> Var i ≡ Var j -> i ≡ j
Var-inj refl = refl

⇒-inj : ∀ {n} {σ₁ σ₂ τ₁ τ₂ : Type n} -> σ₁ ⇒ τ₁ ≡ σ₂ ⇒ τ₂ -> σ₁ ≡ σ₂ × τ₁ ≡ τ₂
⇒-inj refl = refl , refl

instance
  Type-DecEq : ∀ {n} -> DecEq (Type n)
  Type-DecEq = record { _≟_ = _≟ᵗ_ } where
    infix 4 _≟ᵗ_
    _≟ᵗ_ : ∀ {n} -> Decidable (_≡_ {A = Type n})
    Var i   ≟ᵗ Var j   = dcong Var Var-inj (i ≟ j)
    σ₁ ⇒ τ₁ ≟ᵗ σ₂ ⇒ τ₂ = dcong₂ _⇒_ ⇒-inj (σ₁ ≟ᵗ σ₂) (τ₁ ≟ᵗ τ₂)
    Var i   ≟ᵗ σ₂ ⇒ τ₂ = no λ()
    σ₁ ⇒ τ₁ ≟ᵗ Var j   = no λ()

apply-apply : ∀ {n m p} {Φ : Subst m p} {Ψ : Subst n m} σ
            -> apply Φ (apply Ψ σ) ≡ apply (Φ ∘ˢ Ψ) σ
apply-apply (Var i) = refl
apply-apply (σ ⇒ τ) = cong₂ _⇒_ (apply-apply σ) (apply-apply τ)

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
