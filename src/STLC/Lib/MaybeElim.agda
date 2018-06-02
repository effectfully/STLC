module STLC.Lib.MaybeElim where

open import Level
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Unit.Base
open import Data.Bool.Base
open import Data.Maybe.Base

infixl 1  _>>=ᵀ_ _>>=ᵗ_ _>>=⊤_
infixl 4  _<$>ᵗ_
infixr 1  _>=>ᵗ_
infixr 10 _<∘>ᵗ_

data _>>=ᵀ_ {α β} {A : Set α} : (mx : Maybe A) -> (∀ x -> mx ≡ just x -> Set β) -> Set β where
  nothingᵗ : ∀ {B}   ->             nothing >>=ᵀ B
  justᵗ    : ∀ {x B} -> B x refl -> just x  >>=ᵀ B

-- We could write (Set (maybe (const β) zero mx)),
-- but I don't want to introduce dependency at the type level.
FromJustᵗ : ∀ {α β} {A : Set α} {mx : Maybe A} {B : ∀ x -> mx ≡ just x -> Set β}
          -> mx >>=ᵀ B -> Set β
FromJustᵗ  nothingᵗ         = Lift ⊤
FromJustᵗ (justᵗ {x} {B} y) = B x refl

fromJustᵗ : ∀ {α β} {A : Set α} {mx : Maybe A} {B : ∀ x -> mx ≡ just x -> Set β}
          -> (yᵗ : mx >>=ᵀ B) -> FromJustᵗ yᵗ
fromJustᵗ  nothingᵗ = _
fromJustᵗ (justᵗ y) = y

_>>=ᵗ_ : ∀ {α β} {A : Set α} {B : A -> Set β}
       -> (mx : Maybe A) -> (∀ x -> B x) -> mx >>=ᵀ λ x _ -> B x
nothing >>=ᵗ f = nothingᵗ
just  x >>=ᵗ f = justᵗ (f x)

_>>=⊤_ : ∀ {α β} {A : Set α} {B : A -> Set β}
       -> (mx : Maybe A) -> (g : ∀ x -> B x) -> FromJustᵗ (mx >>=ᵗ g)
mx >>=⊤ g = fromJustᵗ $ mx >>=ᵗ g

runᵗ : ∀ {α β} {A : Set α} {mx : Maybe A} {B : ∀ x -> mx ≡ just x -> Set β} {x}
     -> mx >>=ᵀ B -> (p : mx ≡ just x) -> B x p
runᵗ (justᵗ y) refl = y

_<$>ᵗ_ : ∀ {α β γ} {A : Set α} {mx : Maybe A}
           {B : ∀ x -> mx ≡ just x -> Set β}
           {C : ∀ {x} {p : mx ≡ just x} -> B x p -> Set γ}
       -> (∀ {x} {p : mx ≡ just x} -> (y : B x p) -> C y)
       -> (yᵗ : mx >>=ᵀ B)
       -> mx >>=ᵀ λ _ -> C ∘ runᵗ yᵗ
g <$>ᵗ nothingᵗ = nothingᵗ
g <$>ᵗ justᵗ y  = justᵗ (g y)

_>=>ᵗ_ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : ∀ {x} -> B x -> Set γ}
       -> (f : ∀ x -> Maybe (B x))
       -> (∀ {x} -> (y : B x) -> C y)
       -> ∀ x -> f x >>=ᵀ λ y _ -> C y
(f >=>ᵗ g) x = f x >>=ᵗ g

_<∘>ᵗ_ : ∀ {α β γ δ} {A : Set α} {B : A -> Set β} {f : ∀ x -> Maybe (B x)}
           {C : ∀ x y -> f x ≡ just y -> Set γ}
           {D : ∀ {x y} {p : f x ≡ just y} -> C x y p -> Set δ}
       -> (∀ {x y} {p : f x ≡ just y} -> (z : C x y p) -> D z)
       -> (g : ∀ x -> f x >>=ᵀ C x)
       -> ∀ x -> f x >>=ᵀ λ _ -> D ∘ runᵗ (g x)
(h <∘>ᵗ g) x = h <$>ᵗ g x
