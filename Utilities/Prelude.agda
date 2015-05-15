module STLC.Utilities.Prelude where

open import Data.Nat.Base

open import STLC.Library.Prelude public
open import STLC.Library.Membership renaming (here to vz; there to vs_) public

next : ℕ -> ℕ
next = suc
