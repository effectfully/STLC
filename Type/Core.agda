module STLC.Type.Core where

open import STLC.Lib.Prelude
open Membership

infixr 6 _⇒_
infixr 9 _∘ˢ_
infix  4 _∈ᵗ_

data Type n : Set where
  Var : Fin n -> Type n
  _⇒_ : Type n -> Type n -> Type n

Type⁽⁾ : Set
Type⁽⁾ = Type 0

ftv-all : ∀ {n} -> Type n -> List (Fin n)
ftv-all (Var i) = i ∷ []
ftv-all (σ ⇒ τ) = ftv-all σ ++ ftv-all τ

ftv : ∀ {n} -> Type n -> List (Fin n)
ftv = nub ∘ ftv-all

[_/_] : ∀ {n} -> Fin n -> Type n -> Fin n -> Type n
[ i / σ ] j = drec (const σ) (const (Var j)) (i ≟ j)

Subst : ℕ -> ℕ -> Set
Subst n m = Fin n -> Type m

-- Generalize `Type' to `ITree`, make it an instance of `IMonad' and `REWRITE' by the monad laws?
apply : ∀ {n m} -> Subst n m -> Type n -> Type m
apply Ψ (Var i) = Ψ i
apply Ψ (σ ⇒ τ) = apply Ψ σ ⇒ apply Ψ τ

_∘ˢ_ : ∀ {n m p} -> Subst m p -> Subst n m -> Subst n p
Φ ∘ˢ Ψ = apply Φ ∘ Ψ

wkᵗ : ∀ {m n} -> Type n -> Type (n + m)
wkᵗ = apply (Var ∘ inject+ _)

renᵗ : ∀ {n} m -> Type n -> Type (m + n)
renᵗ m = apply (Var ∘ raise m)

SubstInFtv : ∀ {n} -> Type n -> ℕ -> Set
SubstInFtv σ m = ∀ i -> i ∈ ftv σ -> Type m

data _∈ᵗ_ {n} i : Type n -> Set where
  vz : i ∈ᵗ Var i
  vl : ∀ {σ τ} -> i ∈ᵗ σ -> i ∈ᵗ σ ⇒ τ
  vr : ∀ {σ τ} -> i ∈ᵗ τ -> i ∈ᵗ σ ⇒ τ

SubstIn : ∀ {n} -> Type n -> ℕ -> Set
SubstIn σ m = ∀ {i} -> i ∈ᵗ σ -> Type m

runSubstIn : ∀ {n m} {σ : Type n} -> SubstIn σ m -> Type m
runSubstIn {σ = Var i} Ψ = Ψ vz
runSubstIn {σ = σ ⇒ τ} Ψ = runSubstIn (Ψ ∘ vl) ⇒ runSubstIn (Ψ ∘ vr)

thickenⱽ : ∀ {n} -> Fin n -> (σ : Type n) -> Maybe (Fin (length (ftv σ)))
thickenⱽ i = lookup-for i ∘ map swap ∘ enumerate ∘ ftv
