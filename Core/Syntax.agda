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

wkˢ : ∀ {n m} -> Syntax n -> Syntax (n + m)
wkˢ (var i) = var (inject+ _ i)
wkˢ (ƛ b)   = ƛ (wkˢ b)
wkˢ (f · x) = wkˢ f · wkˢ x

Pure : Set
Pure = ∀ {n} -> Syntax n

pure : Syntax⁽⁾ -> Pure
pure e = wkˢ e

shift : ∀ {m} n -> Fin (suc (n + m))
shift  0      = fromℕ _
shift (suc n) = inject₁ (shift n)

Bind : ℕ -> ℕ -> Set
Bind n  0      = Syntax n
Bind n (suc m) = (∀ {p} -> Syntax (suc n + p)) -> Bind (suc n) m

_#_ : ∀ {n} m -> Bind n m -> Syntax n
_#_      zero   b = b
_#_ {n} (suc m) b = ƛ (m # b (var (shift n)))
