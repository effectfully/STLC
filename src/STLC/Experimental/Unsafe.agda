module STLC.Experimental.Unsafe where

open import STLC.Lib.Prelude
open import STLC.Type.Core
open import STLC.Context.Core
open import STLC.Term.Core
open import STLC.Experimental.Safe

module _ where
  private postulate undefined : ∀ {α} {A : Set α} -> A

  UnsafeAssociate : ∀ {α β} {A : Set α} {B : Set β} {{_ : DecEq A}}
                  -> List A -> ((A -> B) -> Set β) -> Set β
  UnsafeAssociate  []      C = C undefined
  UnsafeAssociate (x ∷ xs) C = ∀ {y} ->
    UnsafeAssociate xs λ f -> C λ x' -> if x == x' then y else f x'

  unsafeAssociate : ∀ {α β} {A : Set α} {B : Set β} {{_ : DecEq A}}
                      {C : (A -> B) -> Set β}
                  -> ∀ xs -> (∀ f -> C f) -> UnsafeAssociate xs C
  unsafeAssociate  []      c     = c undefined
  unsafeAssociate (x ∷ xs) c {y} = unsafeAssociate xs λ f -> c λ x' -> if x == x' then y else f x'

  unsafeToSubst : ∀ {n m} {σ : Type n} -> SubstIn σ m -> Subst n m
  unsafeToSubst {σ = σ} Ψ = λ i -> drec Ψ undefined (i ∈ᵗ? σ)

thicken : ∀ {n σ} {Γ : Con n} -> Γ ⊢ σ -> _
thicken {σ = σ} = specialize (unsafeToSubst (thickenˢ σ))

generalize : ∀ {m n} {σ : Type n}
           -> (Γ : Con m) -> Term⁽⁾ σ -> UnsafeAssociate (ftv σ) λ (Ψ : Subst n m) -> Γ ⊢ apply Ψ σ
generalize {σ = σ} _ t = unsafeAssociate (ftv σ) (wk ∘ flip specialize t)

-- -- Just a bit safer, but way more inefficient.
-- generalize : ∀ {m n} {σ : Type n}
--            -> (Γ : Con m) -> Term⁽⁾ σ ->
--                  Associate (ftv σ) λ (Ψ : SubstInFtv σ m) ->
--                     Γ ⊢ apply (unsafeToSubst (fromInFtv σ Ψ)) σ
-- generalize {σ = σ} _ t = associate (ftv σ) λ Ψ -> wk (specialize (unsafeToSubst (fromInFtv σ Ψ)) t)
