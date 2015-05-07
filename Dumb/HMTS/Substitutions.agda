module HMTS.Substitutions where

open import Function
open import Relation.Nullary.Decidable
open import Data.Bool
open import Data.Nat  as Nat
open import Data.Maybe
open import Data.Product
open import Data.List as List

open import HMTS.Prelude
open import HMTS.Types

Subst : Set
Subst = List (ℕ × Type)

apply : Subst -> Type -> Type
apply Ψ (Var i) = maybe′ id (Var i) (lookup i Ψ)
apply Ψ (σ ⇒ τ) = apply Ψ σ ⇒ apply Ψ τ

-- We really need `Data.Set'.
_∘ˢ_ : Subst -> Subst -> Subst
Φ ∘ˢ Ψ =    filter (λ { (i , _) -> not (i ∈? List.map proj₁ Φ) }) Ψ
         ++ List.map (λ{ (i , σ) -> (i , apply Ψ σ) }) Φ 

subst : ℕ -> Type -> Maybe Subst
subst i σ = if i ∈? ftv σ then nothing else just ((i , σ) ∷ [])
