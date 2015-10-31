-- Too ugly.

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

termᵗ : (e : Syntax⁽⁾) -> infer e >>=ᵗ ! λ{ (m , Ψ , t) -> _ }
termᵗ e = ¡ λ{ (m , Ψ , t) -> generalize (thicken (core t)) }

term = fromJustᵗ ∘ termᵗ

-- (generalize ∘ wk) is a bad idea.
termᵗ⁺ : (e : Syntax⁽⁾) -> infer e >>=ᵗ ! λ{ (m , Ψ , t) -> ∀ {Δ} -> _ }
termᵗ⁺ e = ¡ λ{ (m , Ψ , t) -> λ {Δ} -> generalize (wk {Δ = Δ} (thicken (core t))) }

term⁺ = fromJustᵗ ∘ termᵗ⁺

spec-termᵗ : ∀ m' -> (e : Syntax⁽⁾) -> infer e >>=ᵗ ! λ{ (m , Ψ , t) -> _ }
spec-termᵗ m' e = ¡ λ{ (m , Ψ , t) ->
    let t' = thicken (core t) in generalize (widen (m' ∸ upper t') t')
  }

spec-term = λ m' -> fromJustᵗ ∘ spec-termᵗ m'

normᵖᵗ : ∀ {n} (e : Syntax⁽⁾) -> infer e >>=ᵗ ! λ{ (m , Ψ , t) -> _ }
normᵖᵗ {n} e = ¡ λ{ (m , Ψ , t) -> pure (erase (norm (thicken (core t)))) {n} }

normᵖ = λ {n} -> fromJustᵗ ∘ normᵖᵗ {n}

module Names where
  name : ∀ {m} n -> Type (suc n + m)
  name = wkᵗ ∘ Var ∘ fromℕ

  a = λ {m} -> name {m} 0
  b = λ {m} -> name {m} 1
  c = λ {m} -> name {m} 2
  d = λ {m} -> name {m} 3
  e = λ {m} -> name {m} 4
  f = λ {m} -> name {m} 5
  g = λ {m} -> name {m} 6
  h = λ {m} -> name {m} 7
  i = λ {m} -> name {m} 8
  j = λ {m} -> name {m} 9
  k = λ {m} -> name {m} 10
open Names public
