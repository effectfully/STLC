module STLC.Main where

open import STLC.Lib.Prelude  public
open import STLC.Core.Syntax public
open import STLC.Core.Type   public
open import STLC.Core.Term   public
open import STLC.Core.Eval   using (eval)       public
open import STLC.NbE.Main    using (norm)       public
open import STLC.NbE.Read    using (read; inst) public

open import STLC.Lib.MaybeElim
open import STLC.M.Term using (core)
open import STLC.M.Main using (infer)

on-typed : ∀ {α} {A : ∀ {n} {σ : Type n} -> Term⁽⁾ σ -> Set α}
         -> (f : ∀ {n} {σ : Type n} -> (t : Term⁽⁾ σ) -> A t) -> ∀ e -> _
on-typed f e = fromJustᵗ $ infer e >>=ᵗ f ∘ thicken ∘ core ∘ proj₂ ∘ proj₂

typed = on-typed $ id
term  = on-typed $ λ t {m Δ}   -> generalize {m} Δ t
term⁻ = on-typed $ λ {n} t {Δ} -> generalize {n} Δ t
normᵖ = on-typed $ pure ∘ erase ∘ norm

module Names {m} where
  name : ∀ n -> Type (suc n + m)
  name = wkᵗ ∘ Var ∘ fromℕ

  a = name 0
  b = name 1
  c = name 2
  d = name 3
  e = name 4
  f = name 5
  g = name 6
  h = name 7
  i = name 8
  j = name 9
  k = name 10
open Names public
