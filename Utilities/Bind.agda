module STLC.Utilities.Bind where

-- This is a generalization of Conor McBride's cool trick:
-- https://personal.cis.strath.ac.uk/conor.mcbride/fooling/Jigger.agda

open import Function
open import Data.Nat.Base
open import Data.Fin hiding (_+_; #_)

open import STLC.Data.Syntax

shift : ∀ {m} n -> Fin (suc (n + m))
shift  0      = fromℕ _
shift (suc n) = inject₁ (shift n)

Bound : ℕ -> Set
Bound n = ∀ {m} -> Syntax (suc (n + m))

Bindᶜ : (ℕ -> ℕ) -> ℕ -> Set
Bindᶜ k  0      = Syntax (k 0)
Bindᶜ k (suc n) = Bound (k 0) -> Bindᶜ (k ∘ suc) n

bindᶜ : ∀ k n -> Bindᶜ k n -> Syntax (k n)
bindᶜ k  0      b = b
bindᶜ k (suc n) b = bindᶜ (k ∘ suc) n (b (varˢ (shift (k 0))))

ƛⁿ : ∀ {m} n -> Syntax (n + m) -> Syntax m
ƛⁿ  0      e = e
ƛⁿ (suc n) e = ƛⁿ n (ƛˢ e)

_#_ : ∀ {n} m -> Bindᶜ (flip _+_ n) m -> Syntax n
_#_ {n} m b = ƛⁿ m (bindᶜ (flip _+_ n) m b)

private
  example : Syntax 0
  example = 3 # λ h f x → (1 # λ t → t · h) · (f · x)

-- I tried to use instance arguments, but Agda infers wrong types.

-- bind¹ : ∀ {n} -> (Bound n -> Syntax (suc n)) -> Syntax n
-- bind¹ {n} b = ƛˢ (b (varˢ (shift n)))

-- record Bind (B : Set) n : Set where
--   field bind : B -> Syntax n
-- open Bind {{...}}

-- instance
--   stop : ∀ {n} -> Bind (Syntax n) n
--   stop = record { bind = id }

--   keep : ∀ {n} {R : Set} {{_ : Bind R (suc n)}} -> Bind (Bound n -> R) n
--   keep = record { bind = λ r -> bind¹ (bind ∘ r) }
