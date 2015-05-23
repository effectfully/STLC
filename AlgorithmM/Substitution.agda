module STLC.AlgorithmM.Substitution where

open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Data.Empty
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Maybe.Base
open import Data.Product
open import Data.Vec as Vec hiding (_>>=_)

open import STLC.Utilities.Prelude
open import STLC.Data.Type

data Tree {α} (A : Set α) : Set α where
  leaf   : A -> Tree A
  branch : Tree A -> Tree A -> Tree A

Atom : Set
Atom = Maybe (ℕ × Type)

Subst : Set
Subst = Tree Atom

subst-Var : ℕ -> Atom -> Type
subst-Var i ψ = maybe′ id (Var i)
  (ψ >>= λ { (j , σ) -> if i == j then just σ else nothing })

atom-apply : Atom -> Type -> Type
atom-apply ψ (Var i) = subst-Var i ψ
atom-apply ψ (σ ⇒ τ) = atom-apply ψ σ ⇒ atom-apply ψ τ

foldSubst : ∀ {α} {A : Set α} -> (Atom -> A -> A) -> Subst -> A -> A
foldSubst f (leaf   ψ)   x = f ψ x
foldSubst f (branch Φ Ψ) x = foldSubst f Φ (foldSubst f Ψ x)

apply : Subst -> Type -> Type
apply = foldSubst atom-apply

map-apply : ∀ {n} -> Subst -> Conᵛ n -> Conᵛ n
map-apply = foldSubst (Vec.map ∘ atom-apply)

subst-self : ∀ i σ -> subst-Var i (just (i , σ)) ≡ σ
subst-self i σ rewrite ≟-refl i = refl

apply-self : ∀ {τ} i σ -> i ∉ ftv-all σ -> atom-apply (just (i , τ)) σ ≡ σ
apply-self i (Var j) p with j ≟ i
... | no  q           = refl
... | yes q rewrite q = ⊥-elim (p vz)
apply-self i (σ ⇒ τ) p = cong₂ _⇒_
  (apply-self i σ (p ∘ ∈-++₁))
  (apply-self i τ (p ∘ ∈-++₂ (ftv-all σ)))

subst-apply : ∀ i σ -> i ∉ ftv-all σ
            -> subst-Var i (just (i , σ)) ≡ atom-apply (just (i , σ)) σ
subst-apply i σ p rewrite subst-self i σ = sym (apply-self i σ p)

mutual
  ⇒-expand : ∀ Ψ σ τ -> apply Ψ (σ ⇒ τ) ≡ apply Ψ σ ⇒ apply Ψ τ
  ⇒-expand (leaf ψ)     σ τ = refl
  ⇒-expand (branch Φ Ψ) σ τ = ⇒-expand² Φ Ψ σ τ

  ⇒-expand² : ∀ Φ Ψ σ τ
            ->    apply Φ (apply Ψ (σ ⇒ τ))
               ≡ (apply Φ (apply Ψ σ) ⇒ apply Φ (apply Ψ τ))
  ⇒-expand² Φ Ψ σ τ rewrite ⇒-expand Ψ σ τ = ⇒-expand Φ (apply Ψ σ) (apply Ψ τ)

mutual
  ▻ᵛ-expand : ∀ {n} Ψ (Γ : Conᵛ n) σ
           -> map-apply Ψ (Γ ▻ᵛ σ) ≡ map-apply Ψ Γ ▻ᵛ apply Ψ σ
  ▻ᵛ-expand (leaf   ψ)   Γ σ = refl
  ▻ᵛ-expand (branch Φ Ψ) Γ σ = ▻ᵛ-expand² Φ Ψ Γ σ

  ▻ᵛ-expand² : ∀ {n} Φ Ψ (Γ : Conᵛ n) σ
            ->   map-apply Φ (map-apply Ψ (Γ ▻ᵛ σ))
               ≡ map-apply Φ (map-apply Ψ Γ) ▻ᵛ apply Φ (apply Ψ σ)
  ▻ᵛ-expand² Φ Ψ Γ σ rewrite ▻ᵛ-expand Ψ Γ σ = ▻ᵛ-expand Φ (map-apply Ψ Γ) (apply Ψ σ)

compose : ∀ {σ σ' τ τ'} Φ Ψ
        -> apply Ψ  σ                ≡ apply Ψ  σ'
        -> apply Φ (apply Ψ  τ)      ≡ apply Φ (apply Ψ  τ')
        -> apply Φ (apply Ψ (σ ⇒ τ)) ≡ apply Φ (apply Ψ (σ' ⇒ τ'))
compose {σ} {σ'} {τ} {τ'} Φ Ψ p q
  rewrite ⇒-expand² Φ Ψ σ τ | ⇒-expand² Φ Ψ σ' τ' | p | q = refl
