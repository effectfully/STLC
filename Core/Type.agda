module STLC.Core.Type where

open import STLC.Lib.Prelude
open Membership

infixr 6 _⇒_

data Type n : Set where
  Var : Fin n -> Type n
  _⇒_ : Type n -> Type n -> Type n

ftv-all : ∀ {n} -> Type n -> List (Fin n)
ftv-all (Var i) = i ∷ []
ftv-all (σ ⇒ τ) = ftv-all σ ++ ftv-all τ

ftv : ∀ {n} -> Type n -> List (Fin n)
ftv = nub ∘ ftv-all

Subst : ℕ -> ℕ -> Set
Subst n m = Fin n -> Type m

-- Make `Type' an instance of `IMonad' and `REWRITE' by the monad laws?
apply : ∀ {n m} -> Subst n m -> Type n -> Type m
apply Ψ (Var i) = Ψ i
apply Ψ (σ ⇒ τ) = apply Ψ σ ⇒ apply Ψ τ

renᵗ : ∀ {n} m -> Type n -> Type (m + n)
renᵗ m = apply (Var ∘ raise m)

[_/_] : ∀ {n} -> Fin n -> Type n -> Fin n -> Type n
[ i / σ ] j = drec (const σ) (const (Var j)) (i ≟ j)

apply-∘ : ∀ {n m p} {Φ : Subst m p} {Ψ : Subst n m} σ
        -> apply Φ (apply Ψ σ) ≡ apply (apply Φ ∘ Ψ) σ
apply-∘ (Var i) = refl
apply-∘ (σ ⇒ τ) = cong₂ _⇒_ (apply-∘ σ) (apply-∘ τ)
{-# REWRITE apply-∘ #-}

sub-self : ∀ {n σ} -> (i : Fin n) -> [ i / σ ] i ≡ σ
sub-self i rewrite ≟-refl i = refl

non-sub : ∀ {n σ τ} {i : Fin n} -> i ∉ ftv-all σ -> apply [ i / τ ] σ ≡ σ
non-sub {σ = Var j} {i = i} c with i ≟ j
... | yes p rewrite p = ⊥-elim (c here)
... | no  d = refl
non-sub {σ = σ ⇒ τ} c = cong₂ _⇒_ (non-sub (c ∘ ∈-++₁)) (non-sub (c ∘ ∈-++₂ (ftv-all σ)))

sub : ∀ {n} i -> (τ : Type n) -> Maybe (∃ λ (Ψ : Subst n n) -> apply Ψ (Var i) ≡ apply Ψ τ)
sub i σ = drec (const nothing)
               (λ c -> just ([ i / σ ] , right (sub-self i) (non-sub c)))
               (i ∈? ftv-all σ)
