module STLC.Lib.Membership where

open import STLC.Lib.Prelude

infix 4 _∈_ _∉_

data _∈_ {α} {A : Set α} (x : A) : List A -> Set α where
  here  : ∀ {xs}   -> x ∈ x ∷ xs
  there : ∀ {y xs} -> x ∈     xs -> x ∈ y ∷ xs

split-∈ : ∀ {α β} {A : Set α} {B : A -> Set β} {xs : List A} {x y}
        -> (∀ x -> x ∈ xs -> B x) -> B y -> x ∈ y ∷ xs -> B x
split-∈ f z  here     = z
split-∈ f z (there p) = f _ p

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
y ∈? (x ∷ xs) = dJ (λ y x -> y ∈ x ∷ xs)
                   (yes here)
                   (λ c -> dmap there (c ∘∉_) (y ∈? xs))
                   (y ≟ x)

≢-∈-delete : ∀ {α} {A : Set α} {{_ : DecEq A}} {x y} {xs : List A}
           -> x ≢ y -> x ∈ xs -> x ∈ delete y xs
≢-∈-delete {y = y} {x ∷ xs} c  here     with x ≟ y
... | yes p = ⊥-elim (c p)
... | no  d with deletem y xs
... | nothing = here
... | just  _ = here
≢-∈-delete {y = y} {z ∷ xs} c (there p) with z ≟ y
... | yes _ = p
... | no  _ with ≢-∈-delete c p
... | r with deletem y xs
... | nothing = there r
... | just  _ = there r

∈-nub : ∀ {α} {A : Set α} {{_ : DecEq A}} {x} {xs : List A} -> x ∈ xs -> x ∈ nub xs
∈-nub          here         = here
∈-nub {x = x} (there {y} p) with x ≟ y
... | yes q rewrite q = here
... | no  c = there (≢-∈-delete c (∈-nub p))

lookup-for≢nothing : ∀ {α β} {A : Set α} {B : Set β} {{_ : DecEq A}} {x}
                   -> (xs : List (A × B)) -> x ∈ map proj₁ xs -> lookup-for x xs ≢ nothing
lookup-for≢nothing          []             ()
lookup-for≢nothing         ((x , z) ∷ xs)  here     q rewrite ≟-refl x = case q of λ()
lookup-for≢nothing {x = x} ((y , z) ∷ xs) (there p) q with y ≟ x
... | yes _ = case q of λ()
... | no  c = lookup-for≢nothing xs p q

Associate : ∀ {α β} {A : Set α} {B : A -> Set β}
          -> (xs : List A) -> ((∀ x -> x ∈ xs -> B x) -> Set β) -> Set β
Associate  []      C = C (λ _ ())
Associate (x ∷ xs) C = ∀ {y} -> Associate xs λ f -> C λ _ -> split-∈ f y

associate : ∀ {α β} {A : Set α} {B : A -> Set β}
          -> ∀ xs -> {C : (∀ x -> x ∈ xs -> B x) -> Set β} -> (∀ f -> C f) -> Associate xs C
associate  []      c     = c (λ _ ())
associate (x ∷ xs) c {y} = associate xs λ f -> c λ _ -> split-∈ f y
