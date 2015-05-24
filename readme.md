# STLC-in-Agda

## A quick taste

Getting a universe polymorphic Agda function from a pure lambda term: 

```
quacky : Syntax⁽⁾
quacky = 3 # λ a b c → c · (b · a)

Quacky : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
       -> A -> (A -> B) -> (B -> C) -> C
Quacky = eval (compile quacky)
```

`C-c C-n Quacky` gives `λ {.α} {.β} {.γ} {.A} {.B} {.C} y y₁ y₂ → y₂ (y₁ y)`.

## Things

This is simply typed lambda calculus with type variables in Agda. We have raw [Syntax](https://github.com/effectfully/STLC-in-Agda/blob/master/Data/Syntax.agda):

```
data Syntax n : Set where
  varˢ : Fin n -> Syntax n
  ƛˢ_  : Syntax (suc n) -> Syntax n
  _·_  : Syntax n -> Syntax n -> Syntax n
```

[typed terms](https://github.com/effectfully/STLC-in-Agda/blob/master/Data/Term.agda):

```
data _⊢_ (Γ : Con) : Type -> Set where
  var : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _∙_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ
```

and [a mapping](https://github.com/effectfully/STLC-in-Agda/blob/master/AlgorithmM/Main.agda) from the former to the latter via a tweaked version of algorithm M:

```
M : ∀ {n} -> ℕ -> (Γ : Conᵛ n) -> Syntax n -> (σ : Type)
  -> Maybe (ℕ × ∃ λ Ψ -> map-apply Ψ Γ ⊢ apply Ψ σ)
```

`M` receives a context, a term and a type, and checks, whether there is a substitution, that allows to typify the term in this context and with this type, after the substitution is applied to them.

There are also two versions of normalization by evaluation: [the first](https://github.com/effectfully/STLC-in-Agda/blob/master/NbE/Main.agda) is completely stolen from [4] and [the second](https://github.com/effectfully/STLC-in-Agda/blob/master/NbE/LiftableTerms.agda) is described in [5].

There is also [a universe polymorphic eval](https://github.com/effectfully/STLC-in-Agda/blob/master/Eval/Main.agda).

There is also [a cute little trick](https://github.com/effectfully/STLC-in-Agda/blob/master/Utilities/Generalize.agda) to mimic Hindley-Milner generalization. Still, type variables are too rigid.

## References

1. Martin Grabmüller. [Algorithm W Step by Step](https://github.com/wh5a/Algorithm-W-Step-By-Step)
2. Oukseh Lee, Kwangkeun Yi. [A Generalized Let-Polymorphic Type Inference Algorithm](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.41.6832)
3. Dr. Gergő Érdi. [Compositional Type Checking](http://gergo.erdi.hu/projects/tandoori/Tandoori-Compositional-Typeclass.pdf)
4. Nils Anders Danielsson. [Normalisation for the simply typed λ-calculus](http://www.cse.chalmers.se/~nad/listings/simply-typed/)
5. Andreas Abel. [Normalization by Evaluation:
Dependent Types and Impredicativity](http://www2.tcs.ifi.lmu.de/~abel/habil.pdf)