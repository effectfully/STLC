module HMTS.Prelude where

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
open import Data.List.Any
open module M = Membership-≡
open import Data.Vec   as Vec hiding (lookup)
open import Category.Monad
open RawMonad  {{...}} public hiding (pure)

instance
  Maybe-monad : ∀ {ℓ} -> RawMonad {ℓ} Maybe
  Maybe-monad = Maybe.monad

_==_ : ℕ -> ℕ -> Bool
n == m = ⌊ n ≟ m ⌋

lookup : ∀ {α} {A : Set α} -> ℕ -> List (ℕ × A) -> Maybe A
lookup n  []            = nothing
lookup n ((m , x) ∷ xs) = if n == m then just x else lookup n xs

≟-refl : ∀ n -> (n ≟ n) ≡ yes refl
≟-refl  0                         = refl
≟-refl (suc n) rewrite (≟-refl n) = refl

∈-to-Fin : ∀ {α n} {A : Set α} {x} {xs : Vec A n} -> x Vec.∈ xs -> Fin n
∈-to-Fin  here     = Fin.zero
∈-to-Fin (there p) = Fin.suc (∈-to-Fin p)

lookup-in : ∀ {α n} {A : Set α} i -> (xs : Vec A n) -> Vec.lookup i xs Vec.∈ xs
lookup-in  zero   (x ∷ xs) = here
lookup-in (suc i) (x ∷ xs) = there (lookup-in i xs) 

∈-to-Fin∘lookup-in : ∀ {α n} {A : Set α} i (xs : Vec A n)
                   -> ∈-to-Fin (lookup-in i xs) ≡ i
∈-to-Fin∘lookup-in  zero   (x ∷ xs) = refl
∈-to-Fin∘lookup-in (suc i) (x ∷ xs) = cong Fin.suc (∈-to-Fin∘lookup-in i xs)

_∘∉_ : ∀ {m n} {ns : List ℕ} -> m ≢ n -> m ∉ ns -> m ∉ n ∷ ns
_∘∉_ p q (here refl) = p refl
_∘∉_ p q (there r)   = q r

_∈?_ : Decidable (M._∈_)
m ∈?  []      = no λ()
m ∈? (n ∷ ns) with m ≟ n
... | yes p = yes (here p)
... | no  p with m ∈? ns
... | yes q = yes (there q)
... | no  q = no (p ∘∉ q)

delete : ℕ -> List ℕ -> List ℕ
delete n  []      = []
delete n (m ∷ ms) = if n == m then ms else m ∷ delete n ms

nub : List ℕ -> List ℕ
nub ns = List.foldr (λ n r -> n ∷ delete n r) [] ns

∈-++₁ : ∀ {x} {xs ys : List ℕ} -> x M.∈ xs -> x M.∈ xs List.++ ys
∈-++₁ (here refl) = here refl
∈-++₁ (there p)   = there (∈-++₁ p)

∈-++₂ : ∀ {x} {ys : List ℕ} xs -> x M.∈ ys -> x M.∈ xs List.++ ys
∈-++₂  []      p = p
∈-++₂ (x ∷ xs) p = there (∈-++₂ xs p)

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
