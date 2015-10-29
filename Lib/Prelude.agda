module STLC.Lib.Prelude where

open import Level                      renaming (zero to lzero; suc to lsuc)    public
open import Function                   hiding (_∋_)                             public
open import Relation.Nullary                                                    public
open import Relation.Nullary.Decidable hiding (map)                             public
open import Relation.Binary            hiding (_⇒_)                             public
open import Relation.Binary.PropositionalEquality hiding ([_])                  public
open import Data.Empty                                                          public
open import Data.Unit.Base             hiding (_≤_; module _≤_)                 public
open import Data.Bool.Base                                                      public
open import Data.Nat.Base              hiding (_⊔_; erase)                      public
open import Data.Fin                   hiding (_+_; _<_; _≤_; fold; lift; pred) public
open import Data.Sum                   renaming (map to smap)                   public
open import Data.Maybe.Base            hiding (map)                             public
open import Data.List.Base             hiding ([_]; zip; fromMaybe)             public
open import Data.Vec                   using (lookup)                           public

open import STLC.Lib.NoEtaProduct      renaming (map to pmap)                   public

{-# BUILTIN REWRITE _≡_ #-}

import Data.Fin.Properties as FinP
open import Category.Monad
import Data.Maybe as Maybe

private open module Dummy {α} = RawMonad {α} Maybe.monad hiding (pure; zipWith) public

right : ∀ {α} {A : Set α} {x y z : A} -> x ≡ z -> y ≡ z -> x ≡ y
right p q rewrite q = p

fromMaybe : ∀ {α} {A : Set α} -> A -> Maybe A -> A
fromMaybe = maybe id

delim : ∀ {α β} {A : Set α} {B : Dec A -> Set β}
      -> (∀ x -> B (yes x)) -> (∀ c -> B (no c)) -> (d : Dec A) -> B d
delim f g (yes x) = f x
delim f g (no  c) = g c

drec : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> (¬ A -> B) -> Dec A -> B
drec = delim

dmap : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> (¬ A -> ¬ B) -> Dec A -> Dec B
dmap f g = drec (yes ∘ f) (no ∘ g)

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
dcong₂ f inj d₁ d₂ = drec (λ p₁ -> dmap (λ p₂ -> cong₂ f p₁ p₂) (λ c -> c ∘ proj₂ ∘ inj) d₂)
                          (λ c  -> no (c ∘ proj₁ ∘ inj))
                           d₁

record DecEq {α} (A : Set α) : Set α where
  infix 5 _≟_ _==_
  field _≟_ : Decidable (_≡_ {A = A})

  _==_ : A -> A -> Bool
  n == m = ⌊ n ≟ m ⌋

  ≟-refl : ∀ x -> x ≟ x ≡ yes refl
  ≟-refl x with x ≟ x
  ... | yes refl = refl
  ... | no  c    = ⊥-elim (c refl)
open DecEq {{...}} public

instance
  DecEq-Fin : ∀ {n} -> DecEq (Fin n) 
  DecEq-Fin = record { _≟_ = FinP._≟_ }

lookup-for : ∀ {α β} {A : Set α} {B : Set β} {{_ : DecEq A}}
           -> A -> List (A × B) -> Maybe B
lookup-for x  []            = nothing
lookup-for x ((y , z) ∷ xs) = if x == y then just z else lookup-for x xs

deletem : ∀ {α} {A : Set α} {{_ : DecEq A}} -> A -> List A -> Maybe (List A)
deletem x  []      = nothing
deletem x (y ∷ xs) = if x == y then just xs else (y ∷_) <$> deletem x xs

delete : ∀ {α} {A : Set α} {{_ : DecEq A}} -> A -> List A -> List A
delete x xs = fromMaybe xs (deletem x xs)

nub : ∀ {α} {A : Set α} {{_ : DecEq A}} -> List A -> List A
nub = foldr (λ x r -> x ∷ delete x r) []

enumerate : ∀ {α} {A : Set α} -> (xs : List A) -> List (Fin (length xs) × A)
enumerate = go id suc zero where
  go : ∀ {α} {A : Set α}
     -> (k : ℕ -> ℕ)
     -> (∀ {n} -> Fin (k n) -> Fin (k (suc n)))
     -> (∀ {n} -> Fin (k (suc n)))
     -> (xs : List A)
     -> List (Fin (k (length xs)) × A)
  go k s i  []      = []
  go k s i (x ∷ xs) = (i , x) ∷ go (k ∘ suc) s (s i) xs

Associate : ∀ {α β} {A : Set α} {B : Set β} {{_ : DecEq A}}
          -> List A -> (A -> B) -> ((A -> B) -> Set β) -> Set β
Associate  []      inj C = C inj
Associate (x ∷ xs) inj C = ∀ {y} -> Associate xs inj λ c -> C λ x' -> if x == x' then y else c x'

module Membership where
  infix 4 _∈_ _∉_

  data _∈_ {α} {A : Set α} (x : A) : List A -> Set α where
    here  : ∀ {xs}   -> x ∈ x ∷ xs
    there : ∀ {xs y} -> x ∈     xs -> x ∈ y ∷ xs

  _∉_ : ∀ {α} {A : Set α} -> A -> List A -> Set α
  x ∉ xs = ¬ (x ∈ xs)

  _∘∉_ : ∀ {α} {A : Set α} {xs : List A} {x y} -> x ≢ y -> x ∉ xs -> x ∉ y ∷ xs
  _∘∉_ p q  here     = p refl
  _∘∉_ p q (there r) = q r

  ∈-++₁ : ∀ {α} {A : Set α} {xs ys : List A} {x}
        -> x ∈ xs -> x ∈ xs ++ ys
  ∈-++₁  here     = here
  ∈-++₁ (there p) = there (∈-++₁ p)

  ∈-++₂ : ∀ {α} {A : Set α} {ys : List A} {x}
        -> (xs : List A) -> x ∈ ys -> x ∈ xs ++ ys
  ∈-++₂  []      p = p
  ∈-++₂ (x ∷ xs) p = there (∈-++₂ xs p)

  _∈?_ : ∀ {α} {A : Set α} {{_ : DecEq A}} -> Decidable (_∈_ {A = A})
  y ∈?  []      = no λ()
  y ∈? (x ∷ xs) with y ≟ x
  ... | yes p rewrite p = yes here
  ... | no  p = dmap there (p ∘∉_) (y ∈? xs)
