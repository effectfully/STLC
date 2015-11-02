# STLC-in-Agda

## A quick taste

Getting a universe polymorphic Agda function from a pure lambda term: 

```
phoenix : Syntax⁽⁾
phoenix = 4 # λ a b c d → a · (b · d) · (c · d)

phoenixᵗ : Term ((b ⇒ c ⇒ d) ⇒ (a ⇒ b) ⇒ (a ⇒ c) ⇒ a ⇒ d)
phoenixᵗ = term⁻ phoenix

liftM2 : ∀ {α β γ δ} {A : Set α} {B : Set β} {C : Set γ} {D : Set δ}
       -> ((B -> C -> D) -> (A -> B) -> (A -> C) -> A -> D)
liftM2 = eval phoenixᵗ
```

`C-c C-n liftM2` gives `λ {.α} {.β} {.γ} {.δ} {.A} {.B} {.C} {.D} x x₁ x₂ x₃ →
  x (x₁ x₃) (x₂ x₃)`.

## Overview

This is simply typed lambda calculus with type variables in Agda. We have raw [Syntax](https://github.com/effectfully/STLC-in-Agda/blob/master/Core/Syntax.agda):

```
data Syntax n : Set where
  var : Fin n -> Syntax n
  ƛ_  : Syntax (suc n) -> Syntax n
  _·_ : Syntax n -> Syntax n -> Syntax n
```

[typed terms](https://github.com/effectfully/STLC-in-Agda/blob/master/Core/Term.agda):

```
data _⊢_ {n} Γ : Type n -> Set where
  var : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ
```

and [a mapping](https://github.com/effectfully/STLC-in-Agda/blob/master/M/Main.agda) from the former to the latter via a type-safe version of algorithm M:

```
M : ∀ {n l} -> (Γ : Con n l) -> Syntax l -> (σ : Type n)
  -> Maybe (∃ λ m -> ∃ λ (Ψ : Subst n m) -> mapᶜ (apply Ψ) Γ ⊢ apply Ψ σ)
```

`M` receives a context, a term and a type, and checks, whether there is a substitution that allows to typify the term in this context and with this type, after the substitution is applied to them. `M` uses rewrite rules under the hood — this simplifies the definition a lot.

There is an [NbE](https://github.com/effectfully/STLC-in-Agda/blob/master/NbE/Main.agda).

There is [a part](https://github.com/effectfully/STLC-in-Agda/blob/master/NbE/Read.agda) of the liftable terms approach to NbE (described in [4]), which is used to coerce Agda's lambda terms to their first-order counterparts.

There is [a universe polymorphic eval](https://github.com/effectfully/STLC-in-Agda/blob/master/Core/Eval.agda).

Using all this we can, for example, make an Agda lambda term universe polymorphic:

```
mono-app : {A B : Set} -> (A -> B) -> A -> B
mono-app f x = f x

poly-app : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> A -> B
poly-app = eval (read (inst 2 λ A B -> mono-app {A} {B}))
```

## Details

I turned off the eta rule for products, because Agda lacks sharing. My Agda is out of date a bit, so I redefined `Σ` as a `data` instead of placing `{-# NO_ETA Σ #-}` somewhere. Algorithm M is still incredibly slow, and the current `_>>=ᵀ_` eats twice the memory comparing to the previous version, which was more performant, but less usable and inference-friendly, which is important because types signatures are quite verbose.

The [Main](https://github.com/effectfully/STLC-in-Agda/blob/master/Main.agda) module contains

```
on-typed : ∀ {α} {A : ∀ {n} {σ : Type n} -> Term⁽⁾ σ -> Set α}
         -> (f : ∀ {n} {σ : Type n} -> (t : Term⁽⁾ σ) -> A t) -> ∀ e -> _
on-typed f e = fromJustᵗ $ infer e >>=ᵗ f ∘ thicken ∘ core ∘ proj₂ ∘ proj₂

typed = on-typed $ id
term  = on-typed $ λ t {m Δ}   -> generalize {m} Δ t
term⁻ = on-typed $ λ {n} t {Δ} -> generalize {n} Δ t
normᵖ = on-typed $ pure ∘ erase ∘ norm
```

`on-typed` receives a function `f` and a term, tries to typify the term, makes type variables consecutive and strengthened, applies `f` to the result and removes `just`, when inferring is successful, or returns `lift tt` otherwise.

`_>>=ᵗ_` constructs values of type `mx >>=ᵀ B`, which are "either `nothing` or `B x`". The idea is described [here](http://stackoverflow.com/questions/31105947/eliminating-a-maybe-at-the-type-level) (I changed the definition a bit though).

`thicken` is defined in terms of `enumerate` described [here](http://stackoverflow.com/questions/33345899/how-to-enumerate-the-elements-of-a-list-by-fins-in-linear-time).

`generalize` substitutes type variables with universally quantified types with universally quantified upper bounds for variables and prepends a universally quantified context:

```
app : ε {2} ⊢ (Var zero ⇒ Var (suc zero)) ⇒ Var zero ⇒ Var (suc zero)
app = ƛ ƛ var (vs vz) · var vz

gapp : ∀ {n σ τ} {Γ : Con n} -> Γ ⊢ (σ ⇒ τ) ⇒ σ ⇒ τ
gapp = generalize _ app
```

`normᵖ` normalizes a pure lambda term, if it's typeable. Uses NbE under the hood.

## References

1. Martin Grabmüller. [Algorithm W Step by Step](https://github.com/wh5a/Algorithm-W-Step-By-Step)
2. Oukseh Lee, Kwangkeun Yi. [A Generalized Let-Polymorphic Type Inference Algorithm](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.41.6832)
3. Dr. Gergő Érdi. [Compositional Type Checking](http://gergo.erdi.hu/projects/tandoori/Tandoori-Compositional-Typeclass.pdf)
4. Andreas Abel. [Normalization by Evaluation:
Dependent Types and Impredicativity](http://www2.tcs.ifi.lmu.de/~abel/habil.pdf)