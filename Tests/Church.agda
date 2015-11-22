module STLC.Tests.Church where

open import STLC.Main hiding (_·_)
open import STLC.Core.Term using (_·_)

ℕᵗ : ∀ {n} -> Type n -> Type n
ℕᵗ σ = (σ ⇒ σ) ⇒ σ ⇒ σ

zeroᵗ : ∀ {n} {σ : Type n} -> Term (ℕᵗ σ)
zeroᵗ = ƛ ƛ var vz

foldᵗ : ∀ {n} {σ : Type n} -> Term ((σ ⇒ σ) ⇒ σ ⇒ ℕᵗ σ ⇒ σ)
foldᵗ = ƛ ƛ ƛ var vz · var (vs vs vz) · var (vs vz)

sucᵗ : ∀ {n} {σ : Type n} -> Term (ℕᵗ σ ⇒ ℕᵗ σ)
sucᵗ = ƛ ƛ ƛ var (vs vz) · (foldᵗ · (var (vs vz)) · (var vz) · var (vs (vs vz)))

plusᵗ : ∀ {n} {σ : Type n} -> Term (ℕᵗ (ℕᵗ σ) ⇒ ℕᵗ σ ⇒ ℕᵗ σ)
plusᵗ = ƛ ƛ foldᵗ · sucᵗ · var vz · var (vs vz)

Listᵗ : ∀ {n} -> Type n -> Type n -> Type n
Listᵗ σ τ = (σ ⇒ τ ⇒ τ) ⇒ τ ⇒ τ

nilᵗ : ∀ {n} {σ τ : Type n} -> Term (Listᵗ σ τ)
nilᵗ = ƛ ƛ var vz

foldrᵗ : ∀ {n} {σ τ : Type n} -> Term ((σ ⇒ τ ⇒ τ) ⇒ τ ⇒ Listᵗ σ τ ⇒ τ)
foldrᵗ = ƛ ƛ ƛ var vz · var (vs vs vz) · var (vs vz)

consᵗ : ∀ {n} {σ τ : Type n} -> Term (σ ⇒ Listᵗ σ τ ⇒ Listᵗ σ τ)
consᵗ = ƛ ƛ ƛ ƛ var (vs vz) · var (vs vs vs vz)
                            · (foldrᵗ · var (vs vz) · var vz · var (vs (vs vz)))

sumᵗ : ∀ {n} {σ : Type n} -> Term (Listᵗ (ℕᵗ (ℕᵗ σ)) (ℕᵗ σ) ⇒ ℕᵗ σ)
sumᵗ = ƛ foldrᵗ · plusᵗ · zeroᵗ · var vz

module Nums {n σ Γ} where
  0ᵗ = zeroᵗ {n} {σ} {Γ}
  1ᵗ = sucᵗ · 0ᵗ
  2ᵗ = sucᵗ · 1ᵗ
  3ᵗ = sucᵗ · 2ᵗ
  4ᵗ = sucᵗ · 3ᵗ
  5ᵗ = sucᵗ · 4ᵗ
  6ᵗ = sucᵗ · 5ᵗ
open Nums

ex : ∀ {n} {σ τ : Type n} -> Term (Listᵗ (ℕᵗ σ) τ)
ex = consᵗ · 0ᵗ · (consᵗ · 1ᵗ · (consᵗ · 2ᵗ · (consᵗ · 3ᵗ · nilᵗ)))

test : ∀ {n Γ σ} -> norm (sumᵗ · ex) ≡ norm (6ᵗ {n} {σ} {Γ})
test = refl
