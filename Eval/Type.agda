module STLC.Eval.Type where

open import Data.Nat.Base
open import Data.Fin
open import Data.List.Base

infixr 5 _⇒_
infixl 6 _▻_

data Type n : Set where
  Var : Fin n -> Type n
  _⇒_ : Type n -> Type n -> Type n

Con : ℕ -> Set
Con n = List (Type n)

_▻_ : ∀ {n} -> Con n -> Type n -> Con n
Γ ▻ σ = σ ∷ Γ
