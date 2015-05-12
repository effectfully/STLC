module HMTS.Utilities.Prelude where

open import Data.Nat.Base

open import HMTS.Library.Prelude public
open import HMTS.Library.Membership renaming (here to vz; there to vs_) public

next : ℕ -> ℕ
next = suc
