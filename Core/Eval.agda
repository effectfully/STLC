module STLC.Core.Eval where

open import STLC.Lib.Sets
open import STLC.Lib.Prelude
open import STLC.Core.Type
open import STLC.Core.Term

⟦_⟧ᵗˡ : ∀ {n} -> (σ : Type n) -> Level ^ n -> Level
⟦ Var i ⟧ᵗˡ αs = on-^ (lookup i) αs
⟦ σ ⇒ τ ⟧ᵗˡ αs = ⟦ σ ⟧ᵗˡ αs ⊔ ⟦ τ ⟧ᵗˡ αs

⟦_⟧ᵗ : ∀ {n} {αs : Level ^ n} -> (σ : Type n) -> Sets αs -> Set (⟦ σ ⟧ᵗˡ αs)
⟦ Var i ⟧ᵗ As = Lookup i As
⟦ σ ⇒ τ ⟧ᵗ As = ⟦ σ ⟧ᵗ As -> ⟦ τ ⟧ᵗ As

⟦_⟧ᶜˡ : ∀ {n} -> Con n -> Level ^ n -> Level
⟦ ε     ⟧ᶜˡ αs = lzero
⟦ Γ ▻ σ ⟧ᶜˡ αs = ⟦ σ ⟧ᵗˡ αs ⊔ ⟦ Γ ⟧ᶜˡ αs

⟦_⟧ᶜ : ∀ {n} {αs : Level ^ n} -> (Γ : Con n) -> Sets αs -> Set (⟦ Γ ⟧ᶜˡ αs)
⟦ ε     ⟧ᶜ As = ⊤
⟦ Γ ▻ σ ⟧ᶜ As = ⟦ σ ⟧ᵗ As × ⟦ Γ ⟧ᶜ As

lookupᴱ : ∀ {n σ} {Γ : Con n} {αs : Level ^ n} {As : Sets αs}
        -> σ ∈ Γ -> ⟦ Γ ⟧ᶜ As -> ⟦ σ ⟧ᵗ As
lookupᴱ  vz    (x , ρ) = x
lookupᴱ (vs v) (x , ρ) = lookupᴱ v ρ

⟦_⟧ : ∀ {n σ} {Γ : Con n} {αs : Level ^ n} {As : Sets αs}
    -> Γ ⊢ σ -> ⟦ Γ ⟧ᶜ As -> ⟦ σ ⟧ᵗ As
⟦ var v ⟧ ρ = lookupᴱ v ρ
⟦ ƛ b   ⟧ ρ = λ y -> ⟦ b ⟧ (y , ρ)
⟦ f · x ⟧ ρ = ⟦ f ⟧ ρ (⟦ x ⟧ ρ)

eval : ∀ {n} {σ : Type n} {αs : Level ^ n} {As : Sets αs}
     -> Term⁽⁾ σ -> ⟦ σ ⟧ᵗ As
eval t = ⟦ t ⟧ _
