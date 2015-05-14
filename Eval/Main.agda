module HMTS.Eval.Eval where

open import Level as L
open import Function
open import Data.Unit.Base
open import Data.Nat.Base hiding (_⊔_)
open import Data.Fin
open import Data.Product
open import Data.List hiding ([_])
open import Data.Vec  hiding ([_]; _∈_)

open import HMTS.Utilities.Prelude
open import HMTS.Library.Sets
open import HMTS.Eval.Type
open import HMTS.Eval.Term

[_]ᵀᴸ : ∀ {n} -> (σ : Type n) -> Level ^ n -> Level
[ Var i ]ᵀᴸ αs = on-^ (lookup i) αs
[ σ ⇒ τ ]ᵀᴸ αs = [ σ ]ᵀᴸ αs ⊔ [ τ ]ᵀᴸ αs

[_]ᵀ : ∀ {n} {αs : Level ^ n} -> (σ : Type n) -> Sets αs -> Set ([ σ ]ᵀᴸ αs)
[ Var i ]ᵀ As = Lookup i As
[ σ ⇒ τ ]ᵀ As = [ σ ]ᵀ As -> [ τ ]ᵀ As

[_]ᴱᴸ : ∀ {n} -> Con n -> Level ^ n -> Level
[ []    ]ᴱᴸ αs = L.zero
[ σ ∷ Γ ]ᴱᴸ αs = [ σ ]ᵀᴸ αs ⊔ [ Γ ]ᴱᴸ αs

[_]ᴱ : ∀ {n} {αs : Level ^ n} -> (Γ : Con n) -> Sets αs -> Set ([ Γ ]ᴱᴸ αs)
[ []    ]ᴱ As = ⊤
[ σ ∷ Γ ]ᴱ As = [ σ ]ᵀ As × [ Γ ]ᴱ As

lookupᴱ : ∀ {n Γ} {σ : Type n} {αs : Level ^ n} {As : Sets αs}
        -> σ ∈ Γ -> [ Γ ]ᴱ As -> [ σ ]ᵀ As
lookupᴱ  vz    (y , ρ) = y
lookupᴱ (vs v) (y , ρ) = lookupᴱ v ρ

[_] : ∀ {n Γ} {σ : Type n} {αs : Level ^ n} {As : Sets αs}
    -> Γ ⊢ σ -> [ Γ ]ᴱ As -> [ σ ]ᵀ As
[ var v ] ρ = lookupᴱ v ρ
[ ƛ b   ] ρ = λ y -> [ b ] (y , ρ)
[ f ∙ x ] ρ = [ f ] ρ ([ x ] ρ)

evaluate : ∀ {n} {σ : Type n} {αs : Level ^ n} {As : Sets αs}
         -> Term σ -> [ σ ]ᵀ As
evaluate e = [ e ] _
