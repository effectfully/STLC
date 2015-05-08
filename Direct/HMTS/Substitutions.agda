module HMTS.Substitutions where

open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Data.Empty
open import Data.Bool hiding (_≟_)
open import Data.Nat  as Nat
open import Data.Maybe
open import Data.Product
open import Data.List
open import Data.List.Any
open Membership-≡
open import Data.Vec  as Vec hiding (_>>=_; fromList)

open import HMTS.Prelude
open import HMTS.Types

data Tree {α} (A : Set α) : Set α where
  leaf   : A -> Tree A
  branch : Tree A -> Tree A -> Tree A

Atom : Set
Atom = Maybe (ℕ × Type)

Subst : Set
Subst = Tree Atom

fromList : List (ℕ × Type) -> Subst
fromList  []      = leaf nothing
fromList (a ∷ as) = branch (fromList as) (leaf (just a)) 

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

map-apply : ∀ {n} -> Subst -> Con n -> Con n
map-apply = foldSubst (Vec.map ∘ atom-apply)

subst-self : ∀ i σ -> subst-Var i (just (i , σ)) ≡ σ
subst-self i σ rewrite ≟-refl i = refl

apply-self : ∀ {τ} i σ -> i ∉ ftv-all σ -> atom-apply (just (i , τ)) σ ≡ σ
apply-self i (Var j) p with j ≟ i
... | no  q = refl
... | yes q = ⊥-elim (p (here (sym q)))
apply-self i (σ ⇒ τ) p = cong₂ _⇒_
  (apply-self i σ (p ∘ ∈-++₁))
  (apply-self i τ (p ∘ ∈-++₂ (ftv-all σ)))

subst-apply : ∀ i σ -> i ∉ ftv-all σ -> subst-Var i (just (i , σ)) ≡ atom-apply (just (i , σ)) σ
subst-apply i σ p rewrite subst-self i σ = sym (apply-self i σ p)

mutual
  ⇒-expand : ∀ Ψ σ τ -> apply Ψ (σ ⇒ τ) ≡ (apply Ψ σ ⇒ apply Ψ τ)
  ⇒-expand (leaf ψ)     σ τ = refl
  ⇒-expand (branch Φ Ψ) σ τ = ⇒-expand² Φ Ψ σ τ

  ⇒-expand² : ∀ Φ Ψ σ τ -> apply Φ (apply Ψ (σ ⇒ τ)) ≡ (apply Φ (apply Ψ σ) ⇒ apply Φ (apply Ψ τ))
  ⇒-expand² Φ Ψ σ τ rewrite ⇒-expand Ψ σ τ = ⇒-expand Φ (apply Ψ σ) (apply Ψ τ)

mutual
  ▻-expand : ∀ {n} Ψ (Γ : Con n) σ
           -> map-apply Ψ (Γ ▻ σ) ≡ map-apply Ψ Γ ▻ apply Ψ σ
  ▻-expand (leaf   ψ)   Γ σ = refl
  ▻-expand (branch Φ Ψ) Γ σ = ▻-expand² Φ Ψ Γ σ

  ▻-expand² : ∀ {n} Φ Ψ (Γ : Con n) σ
            -> map-apply Φ (map-apply Ψ (Γ ▻ σ)) ≡ map-apply Φ (map-apply Ψ Γ) ▻ apply Φ (apply Ψ σ)
  ▻-expand² Φ Ψ Γ σ rewrite ▻-expand Ψ Γ σ = ▻-expand Φ (map-apply Ψ Γ) (apply Ψ σ)

compose : ∀ {σ σ' τ τ'} Φ Ψ
        -> apply Ψ  σ                ≡ apply Ψ  σ'
        -> apply Φ (apply Ψ  τ)      ≡ apply Φ (apply Ψ  τ')
        -> apply Φ (apply Ψ (σ ⇒ τ)) ≡ apply Φ (apply Ψ (σ' ⇒ τ'))
compose {σ} {σ'} {τ} {τ'} Φ Ψ p q rewrite ⇒-expand² Φ Ψ σ τ | ⇒-expand² Φ Ψ σ' τ' | p | q = refl
