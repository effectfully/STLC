module STLC.Experimental.Safe where

open import STLC.Lib.Prelude
open import STLC.Lib.Membership
open import STLC.Type.Core
open import STLC.Type.Properties

infix  4 _∈ᵗ_

data _∈ᵗ_ {n} i : Type n -> Set where
  vz : i ∈ᵗ Var i
  vl : ∀ {σ τ} -> i ∈ᵗ σ -> i ∈ᵗ σ ⇒ τ
  vr : ∀ {σ τ} -> i ∈ᵗ τ -> i ∈ᵗ σ ⇒ τ

SubstIn : ∀ {n} -> Type n -> ℕ -> Set
SubstIn σ m = ∀ {i} -> i ∈ᵗ σ -> Type m

runSubstIn : ∀ {n m} {σ : Type n} -> SubstIn σ m -> Type m
runSubstIn {σ = Var i} Ψ = Ψ vz
runSubstIn {σ = σ ⇒ τ} Ψ = runSubstIn (Ψ ∘ vl) ⇒ runSubstIn (Ψ ∘ vr)

∈ᵗ-Var : ∀ {n} {i j : Fin n} -> i ∈ᵗ Var j -> i ≡ j
∈ᵗ-Var vz = refl

∈ᵗ-⇒ : ∀ {n i} {σ τ : Type n} -> i ∈ᵗ σ ⇒ τ -> i ∈ᵗ σ ⊎ i ∈ᵗ τ
∈ᵗ-⇒ (vl v) = inj₁ v
∈ᵗ-⇒ (vr v) = inj₂ v

_∈ᵗ?_ : ∀ {n} -> (i : Fin n) -> (σ : Type n) -> Dec (i ∈ᵗ σ)
i ∈ᵗ?  Var j  = dJ (λ i j -> i ∈ᵗ Var j) (yes vz) (λ c -> no (c ∘ ∈ᵗ-Var)) (i ≟ j)
i ∈ᵗ? (σ ⇒ τ) = dsum vl vr (λ c₁ c₂ -> [ c₁ , c₂ ]′ ∘ ∈ᵗ-⇒) (i ∈ᵗ? σ) (i ∈ᵗ? τ)

∈ᵗ-ftv-all : ∀ {n i} {σ : Type n} -> i ∈ᵗ σ -> i ∈ ftv-all σ
∈ᵗ-ftv-all              vz    = here
∈ᵗ-ftv-all             (vl v) = ∈-++₁ (∈ᵗ-ftv-all v)
∈ᵗ-ftv-all {σ = σ ⇒ τ} (vr v) = ∈-++₂ (ftv-all σ) (∈ᵗ-ftv-all v)

∈ᵗ-ftv : ∀ {n i} {σ : Type n} -> i ∈ᵗ σ -> i ∈ ftv σ
∈ᵗ-ftv = ∈-nub ∘ ∈ᵗ-ftv-all

thickenⱽ≢nothing : ∀ {n i} {σ : Type n} -> i ∈ᵗ σ -> thickenⱽ i σ ≢ nothing
thickenⱽ≢nothing {σ = σ} v p with λ q -> lookup-for≢nothing (map swap (enumerate (ftv σ))) q p
... | r rewrite sym (map-compose {g = proj₁} {swap} (enumerate (ftv σ)))
    | map-cong {f = proj₁ ∘ swap} {proj₂} proj₁-swap (enumerate (ftv σ))
    | enumerated (ftv σ) = r (∈ᵗ-ftv v)

fromInFtv : ∀ {n m} -> (σ : Type n) -> SubstInFtv σ m -> SubstIn σ m
fromInFtv _ Ψ = Ψ _ ∘ ∈ᵗ-ftv

thickenˢ : ∀ {n} -> (σ : Type n) -> SubstIn σ (length (ftv σ))
thickenˢ σ {i} v = inspectMaybe (thickenⱽ i σ) (λ i _ -> Var i) (⊥-elim ∘ thickenⱽ≢nothing v)
