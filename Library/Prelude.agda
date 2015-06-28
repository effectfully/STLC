module STLC.Library.Prelude where

open import Level
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit.Base
open import Data.Bool.Base
open import Data.Nat   as Nat hiding (_≟_)
open import Data.Maybe
open import Data.Product
open import Data.List.Base
open import Category.Monad
open RawMonad  {{...}} public hiding (pure)

instance
  Maybe-monad : ∀ {ℓ} -> RawMonad {ℓ} Maybe
  Maybe-monad = monad

record DecEq {α} (A : Set α) : Set α where
  infix 4 _≟_
  field _≟_ : Decidable (_≡_ {A = A})
open DecEq {{...}} public

instance
  DecEq-ℕ : DecEq ℕ
  DecEq-ℕ = record { _≟_ = Nat._≟_ }

_==_ : ∀ {α} {A : Set α} {{_ : DecEq A}} -> A -> A -> Bool
n == m = ⌊ n ≟ m ⌋

lookup-for : ∀ {α β} {A : Set α} {B : Set β} {{_ : DecEq A}}
           -> A -> List (A × B) -> Maybe B
lookup-for x  []            = nothing
lookup-for x ((y , z) ∷ xs) = if x == y then just z else lookup-for x xs

delete : ∀ {α} {A : Set α} {{_ : DecEq A}} -> A -> List A -> List A
delete x  []      = []
delete x (y ∷ xs) = if x == y then xs else y ∷ delete x xs

nub : ∀ {α} {A : Set α} {{_ : DecEq A}} -> List A -> List A
nub = foldr (λ x r -> x ∷ delete x r) []

enumerate : ∀ {α} {A : Set α} -> List A -> List (ℕ × A)
enumerate = go 0 where
  go : ∀ {α} {A : Set α} -> ℕ -> List A -> List (ℕ × A)
  go n  []      = []
  go n (x ∷ xs) = (n , x) ∷ go (ℕ.suc n) xs

Associate : ∀ {γ α β} {A : Set α} {B : Set β}
          -> List A -> (List (A × B) -> Set (β Level.⊔ γ)) -> Set (β Level.⊔ γ)
Associate      []      C = C []
Associate {γ} (x ∷ xs) C = ∀ {y} -> Associate {γ} xs (C ∘ _∷_ (x , y))

≟-refl : ∀ {α} {A : Set α} {{_ : DecEq A}} -> (x : A) -> (x ≟ x) ≡ yes refl
≟-refl x with x ≟ x
... | yes refl = refl
... | no  c    = ⊥-elim (c refl)

dcong : ∀ {α β} {A : Set α} {B : Set β} {x y}
      -> (f : A -> B)
      -> (∀ {x y} -> f x ≡ f y -> x ≡ y)
      -> Dec (x ≡ y)
      -> Dec (f x ≡ f y)
dcong f inj d with d
... | no  p = no (p ∘ inj)
... | yes p = yes (cong f p)

dcong₂ : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} {x y v w}
       -> (f : A -> B -> C)
       -> (∀ {x y} -> f x v ≡ f y w -> x ≡ y × v ≡ w)
       -> Dec (x ≡ y)
       -> Dec (v ≡ w)
       -> Dec (f x v ≡ f y w)
dcong₂ f inj d1 d2 with d1
... | no  p = no (p ∘ proj₁ ∘ inj)
... | yes p with d2
... | no  q = no (q ∘ proj₂ ∘ inj)
... | yes q = yes (cong₂ f p q)

elim-maybeᵖ : ∀ {α β} {A : Set α} {B : Maybe A -> Set β}
            -> (mx : Maybe A) -> (∀ {x} -> mx ≡ just x -> B (just x)) -> B nothing -> B mx
elim-maybeᵖ (just x) f z = f refl
elim-maybeᵖ nothing  f z = z

infixl 3 _>>=ᵗ_ _>>=ₜ_ _>>=ʳ_ _>>=ᵣₜ_

_>>=ᵗ_ : ∀ {α} {A : Set α}
        -> (mx : Maybe A)
           {b : ∀ {x} ->      mx ≡ just x  -> Level}
        -> (B : ∀ {x} -> (r : mx ≡ just x) -> Set (b r))
        -> Set (elim-maybeᵖ mx b Level.zero)
nothing >>=ᵗ B = ⊤
just x  >>=ᵗ B = B refl

_>>=ₜ_ : ∀ {α} {A : Set α}
       -> (mx : Maybe A)
          {b : ∀ {x} ->      mx ≡ just x  -> Level}
          {B : ∀ {x} -> (r : mx ≡ just x) -> Set (b r)}
       -> (f : ∀ {x} -> (r : mx ≡ just x) -> B r)
       -> mx >>=ᵗ B
nothing >>=ₜ f = _
just x  >>=ₜ f = f refl

record _>>=ʳ_ {α} {A : Set α} (mx : Maybe A)
              {b : ∀ {x} ->      mx ≡ just x  -> Level}
              (B : ∀ {x} -> (r : mx ≡ just x) -> Set (b r))
            : Set (elim-maybeᵖ mx b Level.zero) where
  constructor wrapʳ
  field runʳ : mx >>=ᵗ B
open _>>=ʳ_  

reduceᵗ : ∀ {α} {A : Set α} {mx : Maybe A}
            {b : ∀ {x} ->      mx ≡ just x  -> Level}
            {B : ∀ {x} -> (r : mx ≡ just x) -> Set (b r)} {x}
        -> mx >>=ᵗ B -> (r : mx ≡ just x) -> B r
reduceᵗ y refl = y

_>>=ᵣₜ_ : ∀ {α} {A : Set α} {mx : Maybe A}
            {b : ∀ {x} ->      mx ≡ just x  -> Level}
            {B : ∀ {x} -> (r : mx ≡ just x) -> Set (b r)}
            {c : ∀ {x} {r : mx ≡ just x} ->      B r  -> Level}
            {C : ∀ {x} {r : mx ≡ just x} -> (y : B r) -> Set (c y)}
        -> (y : mx >>=ʳ B)
        -> (∀ {x} {r : mx ≡ just x} -> (y : B r) -> C y)
        -> mx >>=ᵗ λ r -> C (reduceᵗ (runʳ y) r)
_>>=ᵣₜ_ {mx = nothing} y g = _
_>>=ᵣₜ_ {mx = just  _} y g = g (runʳ y)
