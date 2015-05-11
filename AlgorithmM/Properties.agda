module HMTS.AlgorithmM.Properties where

open import Relation.Binary.PropositionalEquality
open import Data.Fin
open import Data.Maybe
open import Data.Product
open import Data.Vec as Vec

open import HMTS.Utilities.Prelude
open import HMTS.Data.Syntax
open import HMTS.Data.Type
open import HMTS.AlgorithmM.Substitution
open import HMTS.AlgorithmM.Term
open import HMTS.AlgorithmM.Main

erase-coerceBy : ∀ {n σ τ} {Γ : Conᵛ n} (p : σ ≡ τ) (e : Γ ⊢ σ)
               -> erase (coerceBy p e) ≡ erase e
erase-coerceBy refl e = refl

∈-to-Fin∘atom-specialize-var : ∀ {n σ} {Γ : Conᵛ n} ψ (v : σ ∈ᵛ Γ)
                             -> ∈ᵛ-to-Fin (atom-specialize-var {ψ} v) ≡ ∈ᵛ-to-Fin v
∈-to-Fin∘atom-specialize-var ψ  vz    = refl
∈-to-Fin∘atom-specialize-var ψ (vs v) = cong suc (∈-to-Fin∘atom-specialize-var ψ v)

erase-atom-specialize : ∀ {n σ} {Γ : Conᵛ n} ψ (e : Γ ⊢ σ)
                      -> erase (atom-specialize {ψ} e) ≡ erase e
erase-atom-specialize ψ (var v) = cong varˢ (∈-to-Fin∘atom-specialize-var ψ v)
erase-atom-specialize ψ (ƛ b)   = cong ƛˢ_ (erase-atom-specialize ψ b)
erase-atom-specialize ψ (f ∙ x) = cong₂ _·_
  (erase-atom-specialize ψ f) (erase-atom-specialize ψ x)

erase-specialize : ∀ {n σ} {Γ : Conᵛ n} Ψ (e : Γ ⊢ σ)
                 -> erase (specialize Ψ e) ≡ erase e
erase-specialize (leaf   ψ)   e = erase-atom-specialize ψ e
erase-specialize (branch Φ Ψ) e
  rewrite erase-specialize Φ (specialize Ψ e) = erase-specialize Ψ e

M-sound : ∀ {n} new Γ eˢ σ -> M {n} new Γ eˢ σ >>=ᵀ λ{ (_ , _ , e) -> erase e ≡ eˢ }
M-sound new Γ (varˢ i)  σ
    with U σ (Vec.lookup i Γ)
... | nothing      = _
... | just (Ψ , p)
    rewrite erase-coerceBy (sym p) (specialize Ψ (var (lookup-in i Γ)))
    |       erase-specialize Ψ (var (lookup-in i Γ)) | ∈ᵛ-to-Fin∘lookup-in i Γ = refl
M-sound new Γ (ƛˢ bˢ)   σ
    with U σ (Var new ⇒ Var (next new))
... | nothing      = _
... | just (Ψ , p)
    with M       (next (next new)) (map-apply Ψ (Var new ∷ Γ)) bˢ (apply Ψ (Var (next new)))
    |    M-sound (next (next new)) (map-apply Ψ (Var new ∷ Γ)) bˢ (apply Ψ (Var (next new)))
... | nothing              | q = _
... | just (new'  , Φ , b) | q
    rewrite ▻ᵛ-expand² Φ Ψ Γ (Var new)
    | p   | ⇒-expand²  Φ Ψ (Var new) (Var (next new)) | q = refl
M-sound new Γ (fˢ · xˢ) σ
    with M       (next new) Γ fˢ (Var new ⇒ σ)
    |    M-sound (next new) Γ fˢ (Var new ⇒ σ)
... | nothing              | p = _
... | just (new'  , Ψ , f) | p
    with M       new' (map-apply Ψ Γ) xˢ (apply Ψ (Var new))
    |    M-sound new' (map-apply Ψ Γ) xˢ (apply Ψ (Var new))
... | nothing              | q = _
... | just (new'' , Φ , x) | q
    rewrite ⇒-expand Ψ (Var new) σ
    |       erase-coerceBy (⇒-expand Φ (apply Ψ (Var new)) (apply Ψ σ)) (specialize Φ f)
    |       erase-specialize Φ f | p | q = refl

runM-sound : ∀ eˢ -> runM eˢ >>=ᵀ λ{ (_ , e) -> erase e ≡ eˢ }
runM-sound eˢ with M 1 [] eˢ (Var 0) | M-sound 1 [] eˢ (Var 0) 
... | nothing | _     = _
... | just _  | sound = sound
