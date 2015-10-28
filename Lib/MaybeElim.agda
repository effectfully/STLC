-- Not good.

module STLC.Lib.MaybeElim where

open import Level
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Unit.Base
open import Data.Bool.Base
open import Data.Maybe.Base renaming (is-just to isJust)

infixl 1 _>>=ᵗ_ _>>=ₜ_

data IsJust {α} {A : Set α} : Maybe A -> Set α where
  justIs : ∀ x -> IsJust (just x)

fromIsJust : ∀ {α} {A : Set α} {mx : Maybe A} -> IsJust mx -> A
fromIsJust (justIs x) = x

data _>>=ᵗ_ {α β} {A : Set α} : (mx : Maybe A) -> (IsJust mx -> Set β) -> Set (α ⊔ β) where
  nothingᵗ : ∀ {B} ->                   nothing >>=ᵗ B
  justᵗ    : ∀ {x B} -> B (justIs x) -> just x  >>=ᵗ B

FromJustᵗ : ∀ {α β} {A : Set α} {mx : Maybe A} {B : IsJust mx -> Set β}
          -> mx >>=ᵗ B -> Set β
FromJustᵗ  nothingᵗ         = Lift ⊤
FromJustᵗ (justᵗ {x} {B} y) = B (justIs x)

fromJustᵗ : ∀ {α β} {A : Set α} {mx : Maybe A} {B : IsJust mx -> Set β}
          -> (yᵗ : mx >>=ᵗ B) -> FromJustᵗ yᵗ
fromJustᵗ  nothingᵗ = _
fromJustᵗ (justᵗ y) = y

runᵗ : ∀ {α β} {A : Set α} {mx : Maybe A} {B : IsJust mx -> Set β}
     -> mx >>=ᵗ B -> (imx : IsJust mx) -> B imx
runᵗ (justᵗ y) (justIs x) = y

_<$>ᵗ_ : ∀ {α β γ} {A : Set α} {mx : Maybe A}
           {B : IsJust mx -> Set β} {C : ∀ {imx} -> B imx -> Set γ}
       ->  (∀ {imx} -> (y : B imx) -> C y) -> (yᵗ : mx >>=ᵗ B) -> mx >>=ᵗ C ∘ runᵗ yᵗ
g <$>ᵗ nothingᵗ = nothingᵗ
g <$>ᵗ justᵗ y  = justᵗ (g y)

! : ∀ {α β} {A : Set α} {B : A -> Set β} {mx : Maybe A}
  -> (∀ x -> B x) -> (imx : IsJust mx) -> B (fromIsJust imx)
! f (justIs x) = f x

_>>=ₜ_ : ∀ {α β} {A : Set α} {B : A -> Set β}
       -> (mx : Maybe A) -> (∀ x -> B x) -> mx >>=ᵗ ! B
nothing >>=ₜ f = nothingᵗ
just  x >>=ₜ f = justᵗ (f x)

¡ : ∀ {α β} {A : Set α} {B : A -> Set β} {mx : Maybe A}
  -> (∀ x -> B x) -> mx >>=ᵗ ! B
¡ = _ >>=ₜ_
