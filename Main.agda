module STLC.Main where

open import STLC.Lib.Prelude public
open import STLC.Core.Syntax public
open import STLC.Core.Type   public
open import STLC.Core.Term   public
open import STLC.Core.Eval   public

open import STLC.Lib.MaybeElim
open import STLC.M.Term using (core)
open import STLC.M.Main using (infer)

typify : (e : Syntax⁽⁾) -> infer e >>=ᵗ ! λ{ (m , Ψ , t) -> _ }
typify e = ¡ λ{ (m , Ψ , t) -> thicken (core t) }

term = fromJustᵗ ∘ typify
