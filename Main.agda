-- Too ugly.

module STLC.Main where

open import STLC.Lib.Prelude  public
open import STLC.Core.Syntax public
open import STLC.Core.Type   public
open import STLC.Core.Term   public
open import STLC.Core.Eval   using (eval) public
open import STLC.NbE.Main    using (norm) public
open import STLC.NbE.Read    using (read) public

open import STLC.Lib.MaybeElim
open import STLC.M.Term using (core)
open import STLC.M.Main using (infer)

typifyᵗ : (e : Syntax⁽⁾) -> infer e >>=ᵗ ! λ{ (m , Ψ , t) -> _ }
typifyᵗ e = ¡ λ{ (m , Ψ , t) -> thicken (core t) }

typify = fromJustᵗ ∘ typifyᵗ

normᵖᵗ : ∀ {n} (e : Syntax⁽⁾) -> infer e >>=ᵗ ! λ{ (m , Ψ , t) -> _ }
normᵖᵗ {n} e = ¡ λ{ (m , Ψ , t) -> pure (erase (norm (thicken (core t)))) {n} }

normᵖ = λ {n} -> fromJustᵗ ∘ normᵖᵗ {n}
