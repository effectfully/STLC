module STLC.Type.Properties where

open import STLC.Lib.Prelude
open import STLC.Type.Core
open Membership

Var-inj : ∀ {n} {i j : Fin n} -> Var i ≡ Var j -> i ≡ j
Var-inj refl = refl

⇒-inj : ∀ {n} {σ₁ σ₂ τ₁ τ₂ : Type n} -> σ₁ ⇒ τ₁ ≡ σ₂ ⇒ τ₂ -> σ₁ ≡ σ₂ × τ₁ ≡ τ₂
⇒-inj refl = refl , refl

∈ᵗ-Var : ∀ {n} {i j : Fin n} -> i ∈ᵗ Var j -> i ≡ j
∈ᵗ-Var vz = refl

∈ᵗ-⇒ : ∀ {n i} {σ τ : Type n} -> i ∈ᵗ σ ⇒ τ -> i ∈ᵗ σ ⊎ i ∈ᵗ τ
∈ᵗ-⇒ (vl v) = inj₁ v
∈ᵗ-⇒ (vr v) = inj₂ v

instance
  Type-DecEq : ∀ {n} -> DecEq (Type n)
  Type-DecEq = record { _≟_ = _≟ᵗ_ } where
    infix 4 _≟ᵗ_
    _≟ᵗ_ : ∀ {n} -> Decidable (_≡_ {A = Type n})
    Var i   ≟ᵗ Var j   = dcong Var Var-inj (i ≟ j)
    σ₁ ⇒ τ₁ ≟ᵗ σ₂ ⇒ τ₂ = dcong₂ _⇒_ ⇒-inj (σ₁ ≟ᵗ σ₂) (τ₁ ≟ᵗ τ₂)
    Var i   ≟ᵗ σ₂ ⇒ τ₂ = no λ()
    σ₁ ⇒ τ₁ ≟ᵗ Var j   = no λ()

_∈ᵗ?_ : ∀ {n} -> (i : Fin n) -> (σ : Type n) -> Dec (i ∈ᵗ σ)
i ∈ᵗ?  Var j  = dJ (λ i j -> i ∈ᵗ Var j) (yes vz) (λ c -> no (c ∘ ∈ᵗ-Var)) (i ≟ j)
i ∈ᵗ? (σ ⇒ τ) = dsum vl vr (λ c₁ c₂ -> [ c₁ , c₂ ]′ ∘ ∈ᵗ-⇒) (i ∈ᵗ? σ) (i ∈ᵗ? τ)

apply-apply : ∀ {n m p} {Φ : Subst m p} {Ψ : Subst n m} σ
            -> apply Φ (apply Ψ σ) ≡ apply (Φ ∘ˢ Ψ) σ
apply-apply (Var i) = refl
apply-apply (σ ⇒ τ) = cong₂ _⇒_ (apply-apply σ) (apply-apply τ)

∈ᵗ-ftv-all : ∀ {n i} {σ : Type n} -> i ∈ᵗ σ -> i ∈ ftv-all σ
∈ᵗ-ftv-all              vz    = here
∈ᵗ-ftv-all             (vl v) = ∈-++₁ (∈ᵗ-ftv-all v)
∈ᵗ-ftv-all {σ = σ ⇒ τ} (vr v) = ∈-++₂ (ftv-all σ) (∈ᵗ-ftv-all v)

∈ᵗ-ftv : ∀ {n i} {σ : Type n} -> i ∈ᵗ σ -> i ∈ ftv σ
∈ᵗ-ftv = ∈-nub ∘ ∈ᵗ-ftv-all

fromInFtv : ∀ {n m} -> (σ : Type n) -> SubstInFtv σ m -> SubstIn σ m
fromInFtv _ Ψ = Ψ _ ∘ ∈ᵗ-ftv

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

thickenⱽ≢nothing : ∀ {n i} {σ : Type n} -> i ∈ᵗ σ -> thickenⱽ i σ ≢ nothing
thickenⱽ≢nothing {σ = σ} v p with λ q -> lookup-for≢nothing (map swap (enumerate (ftv σ))) q p
... | r rewrite sym (map-compose {g = proj₁} {swap} (enumerate (ftv σ)))
              | map-cong {f = proj₁ ∘ swap} {proj₂} (λ{ (_ , _) -> refl }) (enumerate (ftv σ))
              | enumerated (ftv σ) = r (∈ᵗ-ftv v)
