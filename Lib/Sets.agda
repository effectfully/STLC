module STLC.Lib.Sets where

open import Level as L
open import Function
open import Data.Unit.Base
open import Data.Nat.Base
open import Data.Fin
open import Data.Product hiding (map)
open import Data.Vec

infixl 6 _^_

_^_ : ∀ {α} -> Set α -> ℕ -> Set α
A ^ 0     = Lift ⊤
A ^ suc n = A × A ^ n

to-^ : ∀ {n α} {A : Set α} -> Vec A n -> A ^ n
to-^ = foldr (_^_ _) _,_ _

from-^ : ∀ {n α} {A : Set α} -> A ^ n -> Vec A n
from-^ {0}      _       = []
from-^ {suc _} (x , xs) = x ∷ from-^ xs

on-^ : ∀ {α β n} {A : Set α} {B : Vec A n -> Set β}
     -> (∀ xs -> B xs) -> ∀ xs -> B (from-^ xs)
on-^ f = f ∘ from-^

mono-^ : ∀ {α n m} {A : Set α} -> (Vec A n -> Vec A m) -> A ^ n -> A ^ m
mono-^ f = to-^ ∘ on-^ f

_⊔ⁿ_ : ∀ {n} -> Level ^ n -> Level -> Level
_⊔ⁿ_ = on-^ $ flip $ foldr _ L._⊔_

Sets : ∀ {n} -> (αs : Level ^ n) -> Set (mono-^ (map L.suc) αs ⊔ⁿ L.zero)
Sets {0}      _       = ⊤
Sets {suc _} (α , αs) = Set α × Sets αs

Lookup : ∀ {n} {αs : Level ^ n} i -> Sets αs -> Set (on-^ (lookup i) αs)
Lookup  zero   (A , As) = A
Lookup (suc i) (A , As) = Lookup i As
