module HMTS.Utilities.Prelude where

open import Level
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Bool  hiding (_≟_)
open import Data.Nat   as Nat
open import Data.Fin
open import Data.Unit  hiding (_≟_)
open import Data.Maybe as Maybe
open import Data.Product
open import Data.List  as List
open import Category.Monad
open RawMonad  {{...}} public hiding (pure)

open import HMTS.Utilities.Membership renaming (here to vz; there to vs_) public

instance
  Maybe-monad : ∀ {ℓ} -> RawMonad {ℓ} Maybe
  Maybe-monad = Maybe.monad

_==_ : ℕ -> ℕ -> Bool
n == m = ⌊ n ≟ m ⌋

lookup-for : ∀ {α} {A : Set α} -> ℕ -> List (ℕ × A) -> Maybe A
lookup-for n  []            = nothing
lookup-for n ((m , x) ∷ xs) = if n == m then just x else lookup-for n xs

delete : ℕ -> List ℕ -> List ℕ
delete n  []      = []
delete n (m ∷ ms) = if n == m then ms else m ∷ delete n ms

nub : List ℕ -> List ℕ
nub ns = List.foldr (λ n r -> n ∷ delete n r) [] ns

≟-refl : ∀ n -> (n ≟ n) ≡ yes refl
≟-refl  0                         = refl
≟-refl (suc n) rewrite (≟-refl n) = refl

_>>=ᵀ_ : ∀ {α} {A : Set α} {b : A -> Level}
       -> (mx : Maybe A) -> (B : ∀ x -> Set (b x)) -> Set (maybe b Level.zero mx)
nothing >>=ᵀ B = ⊤
just x  >>=ᵀ B = B x

_>>=⊤_ : ∀ {α} {A : Set α} {b : A -> Level} {B : ∀ x -> Set (b x)}
       -> (mx : Maybe A) -> (∀ x -> B x) -> mx >>=ᵀ B
nothing >>=⊤ f = _
just x  >>=⊤ f = f x

next : ℕ -> ℕ
next = Nat.suc
