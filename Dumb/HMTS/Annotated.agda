module HMTS.Annotated where

open import Function
open import Data.Nat
open import Data.Fin
open import Data.Product

open import HMTS.Prelude
open import HMTS.Syntax
open import HMTS.Types
open import HMTS.Substitutions

data Annotated n : Set where
  varᵃ : Fin n -> Annotated n 
  ƛᵃ   : Type -> Annotated (suc n) -> Annotated n
  _·ᵃ_ : Annotated n -> Annotated n -> Annotated n

Annotated⁽⁾ : Set
Annotated⁽⁾ = Annotated 0

annotateWith : ∀ {n} -> ℕ -> Subst -> Syntax n -> ℕ × Annotated n
annotateWith new Ψ (varˢ i)  = new , varᵃ i
annotateWith new Ψ (ƛˢ bˢ)   =
  case annotateWith (next (next new)) Ψ bˢ of λ{ (new' , b) ->
  new' , ƛᵃ (apply Ψ (Var new)) b
  }
annotateWith new Ψ (fˢ · xˢ) =
  case annotateWith (next new) Ψ fˢ of λ{ (new'  , f) ->
  case annotateWith  new'      Ψ xˢ of λ{ (new'' , x) ->
  new'' , f ·ᵃ x
  }}

annotate : Subst -> Syntax⁽⁾ -> Annotated⁽⁾ 
annotate Ψ e = proj₂ (annotateWith 1 Ψ e)
