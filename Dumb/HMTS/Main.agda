module HMTS.Main where

open import HMTS.Prelude
open import HMTS.AlgorithmM
open import HMTS.Annotated
open import HMTS.Terms
open import HMTS.Alpha

term : ∀ eᵘ -> 
  infer    eᵘ             >>=ᵀ λ Ψ ->
  typifyᵃ (annotate Ψ eᵘ) >>=ᵀ λ _ ->
  _
term eᵘ =
  infer    eᵘ             >>=⊤ λ Ψ ->
  typifyᵃ (annotate Ψ eᵘ) >>=⊤ λ e ->
  alpha e

open import Data.Nat      public

open import HMTS.Prelude  public
open import HMTS.Syntax   public
open import HMTS.Bind     public
open import HMTS.Types    public
open import HMTS.Names    public
open import HMTS.Terms    public
