module STLC.NbE.Environment where

open import Data.List.Base

open import STLC.Utilities.Prelude
open import STLC.Data.Type

data Env (B : Type -> Set) : Con -> Set where
  Ø    : Env B []
  _▷_ : ∀ {Γ σ} -> Env B Γ -> B σ -> Env B (Γ ▻ σ)

lookup : ∀ {B Γ σ} -> σ ∈ Γ -> Env B Γ -> B σ
lookup  vz    (ρ ▷ y) = y
lookup (vs v) (ρ ▷ y) = lookup v ρ

map-Env : ∀ {B C : Type -> Set} {Γ}
        -> (∀ {σ} -> B σ -> C σ) -> Env B Γ -> Env C Γ
map-Env f  Ø       = Ø
map-Env f (ρ ▷ y) = map-Env f ρ ▷ f y
