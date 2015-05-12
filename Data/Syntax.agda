module HMTS.Data.Syntax where

open import Data.Nat.Base
open import Data.Fin hiding (_+_)

infixl 5 _·_

data Syntax n : Set where
  varˢ : Fin n -> Syntax n
  ƛˢ_  : Syntax (suc n) -> Syntax n
  _·_  : Syntax n -> Syntax n -> Syntax n

Syntax⁽⁾ : Set
Syntax⁽⁾ = Syntax 0

weaken : ∀ {n m} -> Syntax n -> Syntax (n + m)
weaken (varˢ i) = varˢ (inject+ _ i)
weaken (ƛˢ b)   = ƛˢ weaken b
weaken (f · x)  = weaken f · weaken x

Pure : Set
Pure = ∀ {n} -> Syntax n

pure : Syntax⁽⁾ -> Pure
pure e = weaken e
