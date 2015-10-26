module STLC.Core.Syntax where

open import STLC.Lib.Prelude

infix  3  ƛ_
infixl 6  _·_
infix  10 _#_

data Syntax n : Set where
  var : Fin n -> Syntax n
  ƛ_  : Syntax (suc n) -> Syntax n
  _·_ : Syntax n -> Syntax n -> Syntax n

Syntax⁽⁾ : Set
Syntax⁽⁾ = Syntax 0

ren : ∀ {n m} -> Syntax n -> Syntax (n + m)
ren (var i) = var (inject+ _ i)
ren (ƛ b)   = ƛ ren b
ren (f · x)  = ren f · ren x

Pure : Set
Pure = ∀ {n} -> Syntax n

pure : Syntax⁽⁾ -> Pure
pure e = ren e

shift : ∀ {m} n -> Fin (suc (n + m))
shift  0      = fromℕ _
shift (suc n) = inject₁ (shift n)

Bindᶜ : (ℕ -> ℕ) -> ℕ -> Set
Bindᶜ k  0      = Syntax (k 0)
Bindᶜ k (suc n) = (∀ {m} -> Syntax (suc (k 0 + m))) -> Bindᶜ (k ∘ suc) n

bindᶜ : ∀ k n -> Bindᶜ k n -> Syntax (k n)
bindᶜ k  0      b = b
bindᶜ k (suc n) b = bindᶜ (k ∘ suc) n (b (var (shift (k 0))))

ƛⁿ : ∀ {m} n -> Syntax (n + m) -> Syntax m
ƛⁿ  0      e = e
ƛⁿ (suc n) e = ƛⁿ n (ƛ e)

_#_ : ∀ {n} m -> Bindᶜ (flip _+_ n) m -> Syntax n
_#_ {n} m b = ƛⁿ m (bindᶜ (flip _+_ n) m b)
