module STLC.Core.Eval where

open import STLC.Lib.Sets
open import STLC.Lib.Prelude
open import STLC.Core.Type
open import STLC.Core.Term

⟦_⟧ᵗˡ : ∀ {n} σ -> Level ^ n -> Level
⟦ Var i ⟧ᵗˡ αs = on-^ (lookup i) αs
⟦ σ ⇒ τ ⟧ᵗˡ αs = ⟦ σ ⟧ᵗˡ αs ⊔ ⟦ τ ⟧ᵗˡ αs

⟦_⟧ᵗ : ∀ {n} {αs : Level ^ n} σ -> Sets αs -> Set (⟦ σ ⟧ᵗˡ αs)
⟦ Var i ⟧ᵗ As = Lookup i As
⟦ σ ⇒ τ ⟧ᵗ As = ⟦ σ ⟧ᵗ As -> ⟦ τ ⟧ᵗ As

⟦_⟧ᶜˡ : ∀ {n} -> Con n -> Level ^ n -> Level
⟦ ε     ⟧ᶜˡ αs = lzero
⟦ Γ ▻ σ ⟧ᶜˡ αs = ⟦ σ ⟧ᵗˡ αs ⊔ ⟦ Γ ⟧ᶜˡ αs

⟦_⟧ᶜ : ∀ {n} {αs : Level ^ n} Γ -> Sets αs -> Set (⟦ Γ ⟧ᶜˡ αs)
⟦ ε     ⟧ᶜ As = ⊤
⟦ Γ ▻ σ ⟧ᶜ As = ⟦ σ ⟧ᵗ As × ⟦ Γ ⟧ᶜ As

lookupᵉ : ∀ {n Γ σ} {αs : Level ^ n} {As : Sets αs} -> σ ∈ Γ -> ⟦ Γ ⟧ᶜ As -> ⟦ σ ⟧ᵗ As
lookupᵉ  vz    (x , ρ) = x
lookupᵉ (vs v) (x , ρ) = lookupᵉ v ρ

⟦_⟧ : ∀ {n Γ σ} {αs : Level ^ n} {As : Sets αs} -> Γ ⊢ σ -> ⟦ Γ ⟧ᶜ As -> ⟦ σ ⟧ᵗ As
⟦ var v ⟧ ρ = lookupᵉ v ρ
⟦ ƛ b   ⟧ ρ = λ x -> ⟦ b ⟧ (x , ρ)
⟦ f · x ⟧ ρ = ⟦ f ⟧ ρ (⟦ x ⟧ ρ)

eval : ∀ {n σ} {αs : Level ^ n} {As : Sets αs} -> Term⁽⁾ σ -> ⟦ σ ⟧ᵗ As
eval t = ⟦ t ⟧ _
