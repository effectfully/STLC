module HMTS.Tests.Church where

open import Relation.Binary.PropositionalEquality

open import HMTS.Main

z : Pure
z = pure (2 # λ f z → z)

s : Pure
s = pure (3 # λ n f z → f · (n · f · z))

plus : Pure
plus = pure (4 # λ n m f z → n · f · (m · f · z))

ex1 : Pure
ex1 = plus · (s · z) · (plus · z · (s · (s · z)))

open import Data.Fin

-- typing C-c C-n

--   norm ex1

-- will give you

--   ƛˢ ƛˢ varˢ (suc zero) · (varˢ (suc zero) · (varˢ (suc zero) · varˢ zero))

nil : Pure
nil = pure (2 # λ f z → z)

foldr : Pure
foldr = pure (3 # λ f z xs → xs · f · z)

cons : Pure
cons = pure (4 # λ x xs f z → f · x · (foldr · f · z · xs))

sum : Pure
sum = foldr · plus · z

-- Agda can't normalize this on my machine.
ex2 : Pure
ex2 = sum · (cons · (s · z) · (cons · (s · (s · z)) · nil))
