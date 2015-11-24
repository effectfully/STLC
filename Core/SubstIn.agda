module STLC.Core.SubstIn where

open import STLC.Lib.Prelude
open import STLC.Core.Type
open Membership

infix 4 _∈ᵗ_

data _∈ᵗ_ {n} i : Type n -> Set where
  vz : i ∈ᵗ Var i
  vl : ∀ {σ τ} -> i ∈ᵗ σ -> i ∈ᵗ σ ⇒ τ
  vr : ∀ {σ τ} -> i ∈ᵗ τ -> i ∈ᵗ σ ⇒ τ

SubstIn : ∀ {n} -> Type n -> ℕ -> Set
SubstIn σ m = ∀ {i} -> i ∈ᵗ σ -> Type m

runSubstIn : ∀ {n m} {σ : Type n} -> SubstIn σ m -> Type m
runSubstIn {σ = Var i} Ψ = Ψ vz
runSubstIn {σ = σ ⇒ τ} Ψ = runSubstIn (Ψ ∘ vl) ⇒ runSubstIn (Ψ ∘ vr)

∈ᵗ-ftv-all : ∀ {n i} {σ : Type n} -> i ∈ᵗ σ -> i ∈ ftv-all σ
∈ᵗ-ftv-all              vz    = here
∈ᵗ-ftv-all             (vl v) = ∈-++₁ (∈ᵗ-ftv-all v)
∈ᵗ-ftv-all {σ = σ ⇒ τ} (vr v) = ∈-++₂ (ftv-all σ) (∈ᵗ-ftv-all v)

thickenⱽ : ∀ {n} -> Fin n -> (σ : Type n) -> Maybe (Fin (length (ftv σ)))
thickenⱽ i = lookup-for i ∘ map swap ∘ enumerate ∘ ftv

thickenⱽ≢nothing : ∀ {n i} {σ : Type n} -> i ∈ᵗ σ -> thickenⱽ i σ ≢ nothing
thickenⱽ≢nothing {σ = σ} v p with λ q -> lookup-for≢nothing (map swap (enumerate (ftv σ))) q p
... | r rewrite sym (map-compose {g = proj₁} {swap} (enumerate (ftv σ)))
              | map-cong {f = proj₁ ∘ swap} {proj₂} (λ{ (_ , _) -> refl }) (enumerate (ftv σ))
              | enumerated (ftv σ) = r (∈-nub (∈ᵗ-ftv-all v))

thickenInˢ : ∀ {n} -> (σ : Type n) -> SubstIn σ (length (ftv σ))
thickenInˢ σ = λ {i} v -> inspectMaybe (thickenⱽ i σ) (λ i _ -> Var i) (⊥-elim ∘ thickenⱽ≢nothing v)
