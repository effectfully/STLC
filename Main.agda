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

typifyᵗ = infer >=>ᵗ thicken ∘ core ∘ proj₂ ∘ proj₂

term  = fromJustᵗ ∘ (λ t {Δ} -> generalize Δ t)             <∘>ᵗ typifyᵗ
term⁺ = fromJustᵗ ∘ (λ t {d Δ} -> generalize Δ (widen d t)) <∘>ᵗ typifyᵗ
normᵖ = fromJustᵗ ∘ (pure ∘ erase ∘ norm)                   <∘>ᵗ typifyᵗ

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
