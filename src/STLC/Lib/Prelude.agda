{-# OPTIONS --rewriting #-}

module STLC.Lib.Prelude where

open import Level                      renaming (zero to lzero; suc to lsuc)               public
open import Function                   hiding (_∋_)                                        public
open import Relation.Nullary                                                               public
open import Relation.Nullary.Decidable hiding (map)                                        public
open import Relation.Binary            hiding (_⇒_)                                        public
open import Relation.Binary.PropositionalEquality hiding ([_])                             public
open import Data.Empty                                                                     public
open import Data.Unit.Base             hiding (_≤_; module _≤_)                            public
open import Data.Bool.Base             hiding (_≟_)                                        public
open import Data.Nat.Base              hiding (_≟_; _⊔_; _^_; erase; Ordering; compare)    public
open import Data.Fin                   hiding (_≟_; _+_; _<_; _≤_; _≤?_; fold; lift; pred) public
open import Data.Sum                   hiding (swap) renaming (map to smap)                public
open import Data.Maybe.Base            hiding (map)                                        public
open import Data.List.Base             hiding ([_]; lookup; zip; fromMaybe; tabulate)      public
open import Data.List.Properties                                                           public
open import Data.Vec                   using (Vec; []; _∷_; lookup; tabulate)              public
open import Data.Vec.N-ary             renaming (_$ⁿ_ to _$ᵗⁿ_)                            public

open import STLC.Lib.NoEtaProduct      renaming (map to pmap)                              public

{-# BUILTIN REWRITE _≡_ #-}

import Data.Fin.Properties as FinP
open import Category.Monad
import Data.Maybe as Maybe

private open module Dummy {α} = RawMonad {α} Maybe.monad hiding (pure; zipWith) public

record Wrap {α} (A : Set α) : Set α where
  constructor wrap
  field unwrap : A
open Wrap public

infixl 10 _%
infixl 2  _>>>_

_% = _∘_

_>>>_ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : ∀ {x} -> B x -> Set γ}
      -> (f : (x : A) -> B x) -> (∀ {x} -> (y : B x) -> C y) -> ∀ x -> C (f x)
f >>> g = g ∘ f

right : ∀ {α} {A : Set α} {x y z : A} -> x ≡ z -> y ≡ z -> x ≡ y
right p q rewrite q = p

fromMaybe : ∀ {α} {A : Set α} -> A -> Maybe A -> A
fromMaybe = maybe id

first : ∀ {α β γ} {A : Set α} {B : Set β} {C : A -> Set γ}
      -> (∀ x -> C x) -> (p : A × B) -> C (proj₁ p) × B
first f (x , y) = f x , y

second : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ}
       -> (∀ {x} -> B x -> C x) -> Σ A B -> Σ A C
second g (x , y) = , g y

inspectMaybe : ∀ {α β} {A : Set α} {B : Maybe A -> Set β}
             -> (mx : Maybe A)
             -> (∀ x -> mx ≡ just x -> B (just x))
             -> (mx ≡ nothing -> B nothing)
             -> B mx
inspectMaybe  nothing g f = f refl
inspectMaybe (just x) g f = g x refl

delim : ∀ {α β} {A : Set α} {B : Dec A -> Set β}
      -> (∀ x -> B (yes x)) -> (∀ c -> B (no c)) -> (d : Dec A) -> B d
delim f g (yes x) = f x
delim f g (no  c) = g c

drec : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> (¬ A -> B) -> Dec A -> B
drec = delim

dmap : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> (¬ A -> ¬ B) -> Dec A -> Dec B
dmap f g = drec (yes ∘ f) (no ∘ g)

ddsum : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
      -> (A -> Dec C) -> (B -> Dec C) -> (¬ A -> ¬ B -> Dec C) -> Dec A -> Dec B -> Dec C
ddsum f g h d₁ d₂ = drec f (λ c -> drec g (h c) d₂) d₁

ddprod : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
       -> (A -> B -> Dec C) -> (¬ A -> Dec C) -> (¬ B -> Dec C) -> Dec A -> Dec B -> Dec C
ddprod h f g d₁ d₂ = drec (λ x -> drec (h x) g d₂) f d₁

dsum : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
     -> (A -> C) -> (B -> C) -> (¬ A -> ¬ B -> ¬ C) -> Dec A -> Dec B -> Dec C
dsum f g h = ddsum (yes ∘ f) (yes ∘ g) (no % ∘ h)

dprod : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
      -> (A -> B -> C) -> (¬ A -> ¬ C) -> (¬ B -> ¬ C) -> Dec A -> Dec B -> Dec C
dprod h f g = ddprod (yes % ∘ h) (no ∘ f) (no ∘ g)

dcong : ∀ {α β} {A : Set α} {B : Set β} {x y}
      -> (f : A -> B)
      -> (∀ {x y} -> f x ≡ f y -> x ≡ y)
      -> Dec (x ≡ y)
      -> Dec (f x ≡ f y)
dcong f inj = dmap (cong f) (_∘ inj)

dcong₂ : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} {x y v w}
       -> (f : A -> B -> C)
       -> (∀ {x y} -> f x v ≡ f y w -> x ≡ y × v ≡ w)
       -> Dec (x ≡ y)
       -> Dec (v ≡ w)
       -> Dec (f x v ≡ f y w)
dcong₂ f inj = dprod (cong₂ f) (λ c -> c ∘ proj₁ ∘ inj) (λ c -> c ∘ proj₂ ∘ inj)

dJ : ∀ {α β} {A : Set α} {x y}
   -> (B : A -> A -> Set β)
   -> Dec (B x x)
   -> (x ≢ y -> Dec (B x y))
   -> Dec (x ≡ y)
   -> Dec (B x y)
dJ B y f (yes refl) = y
dJ B y f (no  c)    = f c

record DecEq {α} (A : Set α) : Set α where
  infix 5 _≟_ _==_
  field _≟_ : Decidable (_≡_ {A = A})

  _==_ : A -> A -> Bool
  n == m = ⌊ n ≟ m ⌋

  ≟-refl : ∀ x -> x ≟ x ≡ yes refl
  ≟-refl x with x ≟ x
  ... | yes refl = refl
  ... | no  c    = ⊥-elim (c refl)

  ≢-no : ∀ {x y} -> x ≢ y -> ∃ λ c -> x ≟ y ≡ no c
  ≢-no {x} {y} c with x ≟ y
  ... | yes p = ⊥-elim (c p)
  ... | no  d = d , refl
open DecEq {{...}} public

instance
  DecEq-Fin : ∀ {n} -> DecEq (Fin n)
  DecEq-Fin = record { _≟_ = FinP._≟_ }

lookup-for : ∀ {α β} {A : Set α} {B : Set β} {{_ : DecEq A}}
           -> A -> List (A × B) -> Maybe B
lookup-for x  []            = nothing
lookup-for x ((y , z) ∷ xs) = if y == x then just z else lookup-for x xs

-- It should be (List A ⊎ List A).
deletem : ∀ {α} {A : Set α} {{_ : DecEq A}} -> A -> List A -> Maybe (List A)
deletem x  []      = nothing
deletem x (y ∷ xs) = if y == x then just xs else (y ∷_) <$> deletem x xs

delete : ∀ {α} {A : Set α} {{_ : DecEq A}} -> A -> List A -> List A
delete x xs = fromMaybe xs (deletem x xs)

nub : ∀ {α} {A : Set α} {{_ : DecEq A}} -> List A -> List A
nub = foldr (λ x r -> x ∷ delete x r) []

proj₁-swap : ∀ {α β} {A : Set α} {B : Set β} -> (p : A × B) -> proj₁ (swap p) ≡ proj₂ p
proj₁-swap (_ , _) = refl

module Enumerate where
  go : ∀ {α} {A : Set α}
     -> (k : ℕ -> ℕ)
     -> (∀ {n} -> Fin (k n) -> Fin (k (suc n)))
     -> (∀ {n} -> Fin (k (suc n)))
     -> (xs : List A)
     -> List (Fin (k (length xs)) × A)
  go k s i  []      = []
  go k s i (x ∷ xs) = (i , x) ∷ go (k ∘ suc) s (s i) xs

  enumerate : ∀ {α} {A : Set α} -> (xs : List A) -> List (Fin (length xs) × A)
  enumerate = go id suc zero

  goed : ∀ {α} {A : Set α} {k : ℕ -> ℕ}
           {s : ∀ {n} -> Fin (k n) -> Fin (k (suc n))}
           {i : ∀ {n} -> Fin (k (suc n))}
       -> (xs : List A) -> map proj₂ (go k s i xs) ≡ xs
  goed  []      = refl
  goed (x ∷ xs) = cong (x ∷_) (goed xs)

  enumerated : ∀ {α} {A : Set α} -> (xs : List A) -> map proj₂ (enumerate xs) ≡ xs
  enumerated = goed
open Enumerate using (enumerate; enumerated) public

_$ⁿ_ : ∀ {α β n} {A : Set α} {F : N-ary n A (Set β)} -> ∀ⁿ n F -> (xs : Vec _ n) -> F $ᵗⁿ xs
y $ⁿ  []      = y
f $ⁿ (x ∷ xs) = f x $ⁿ xs

_$ⁿʰ_ : ∀ {α β n} {A : Set α} {F : N-ary n A (Set β)} -> ∀ⁿʰ n F -> (xs : Vec _ n) -> F $ᵗⁿ xs
y $ⁿʰ  []      = y
y $ⁿʰ (x ∷ xs) = y $ⁿʰ xs
