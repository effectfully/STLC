# HMTS-in-Agda

It's a Hindley-Milner type system in Agda. We have untyped terms:

```
data Syntax n : Set where
  varˢ : Fin n -> Syntax n
  ƛˢ_  : Syntax (suc n) -> Syntax n
  _·_  : Syntax n -> Syntax n -> Syntax n
```

typed terms (this version is from the [/Direct/HMTS/Terms](https://github.com/effectfully/HMTS-in-Agda/tree/master/Direct/HMTS/Terms) module;
the version from the [/Dumb/HMTS/Terms](https://github.com/effectfully/HMTS-in-Agda/tree/master/Dumb/HMTS/Terms) module uses lists instead of vectors):

```
data _⊢_ {n} (Γ : Con n) : Type -> Set where
  var : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _∙_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ
```

and a function, that maps the former to the latter.

There are two versions: Dumb and Direct. The Dumb version proceeds as follows:

 1. Infer a substitution using algorithm M.
 2. Annotate every lambda in the term with an appropriate type variable and apply the inferred substitution to it.
 3. Typify the annotated term.
 
We have no guarantees, that annotated term is actually well-typed, so the result of the third step is wrapped in the Maybe monad.

The Direct version instead uses a tweaked version of algorithm M (I don't know, whether it has a proper name)
with pretty self-describing type signature (ignore the `ℕ ×` part — it's about fresh names):

```
M : ∀ {n} -> ℕ -> (Γ : Con n) -> Syntax n -> (σ : Type)
  -> Maybe (ℕ × ∃ λ Ψ -> map-apply Ψ Γ ⊢ apply Ψ σ)
```

I.e. `M` receives a context, a term and a type, and checks, whether there is a substitution,
that allows to typify the term in this context and with this type, after the substitution is applied to them.
Soundness of `M` is proved in the [Properties](https://github.com/effectfully/HMTS-in-Agda/tree/master/Direct/HMTS/Properties.agda) module.
