module STLC.Lib.MaybeElim where

open import Level
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Unit.Base
open import Data.Bool.Base
open import Data.Maybe.Base renaming (is-just to isJust)

IsJust : ∀ {α} {A : Set α} -> Maybe A -> Set
IsJust = T ∘ isJust

infixl 1 _>>=ᵗ_
infixl 5 _<$>ᵗ_

data _>>=ᵗ_ {α β} {A : Set α} : (mx : Maybe A) -> (IsJust mx -> Set β) -> Set (α ⊔ β) where
  nothingᵗ : ∀ {B}   ->        nothing >>=ᵗ B
  justᵗ    : ∀ {B x} -> B _ -> just x  >>=ᵗ B

FromJustᵗ : ∀ {α β} {A : Set α} {mx : Maybe A} {B : IsJust mx -> Set β}
          -> mx >>=ᵗ B -> Set β
FromJustᵗ  nothingᵗ     = Lift ⊤
FromJustᵗ (justᵗ {B} y) = B _

fromJustᵗ : ∀ {α β} {A : Set α} {mx : Maybe A} {B : IsJust mx -> Set β}
          -> (yᵗ : mx >>=ᵗ B) -> FromJustᵗ yᵗ
fromJustᵗ  nothingᵗ = _
fromJustᵗ (justᵗ y) = y

runᵗ : ∀ {α β} {A : Set α} {mx : Maybe A} {B : IsJust mx -> Set β}
     -> mx >>=ᵗ B -> (imx : IsJust mx) -> B imx
runᵗ  nothingᵗ ()
runᵗ (justᵗ y) _  = y

_<$>ᵗ_ : ∀ {α β γ} {A : Set α} {mx : Maybe A} {B : IsJust mx -> Set β} {C : ∀ {x} -> B x -> Set γ}
       -> (∀ {x} -> (y : B x) -> C y) -> (yᵗ : mx >>=ᵗ B) -> mx >>=ᵗ C ∘ runᵗ yᵗ
g <$>ᵗ nothingᵗ = nothingᵗ
g <$>ᵗ justᵗ y  = justᵗ (g y)

!′ : ∀ {α β} {A : Set α} {B : ∀ {mx} -> IsJust mx -> Set β} {mx : Maybe A}
   -> (∀ x -> mx ≡ just x -> B {just x} _) -> (imx : IsJust mx) -> B imx
!′ {mx = nothing} f ()
!′ {mx = just x } f _  = f x refl

¡′ : ∀ {α β} {A : Set α} {B : A -> Set β} {mx : Maybe A}
   -> (∀ x -> mx ≡ just x -> B x) -> mx >>=ᵗ !′ (const ∘ B)
¡′ {mx = nothing} f = nothingᵗ
¡′ {mx = just  x} f = justᵗ (f x refl)

! : ∀ {α β} {A : Set α} {B : ∀ {mx} -> IsJust mx -> Set β} {mx : Maybe A}
  -> (∀ x -> B {just x} _) -> (imx : IsJust mx) -> B imx
! {B = B} f = !′ {B = B} (const ∘ f)

¡_ : ∀ {α β} {A : Set α} {B : A -> Set β} {mx : Maybe A}
   -> (∀ x -> B x) -> mx >>=ᵗ ! B
¡ f = ¡′ (const ∘ f)
