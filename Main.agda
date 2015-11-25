module STLC.Main where

open import STLC.Lib.Prelude                         public
open import STLC.Term.Syntax                         public
open import STLC.Term                                public
open import STLC.Semantics.Eval   using (eval)       public
open import STLC.NbE.Main         using (norm)       public
open import STLC.NbE.Read         using (read; inst) public

open import STLC.Lib.MaybeElim
open import STLC.M.Term using (core)

module NF where
  open import STLC.M.Typecheck using (runM; typecheck)

  -- If `e' is in NF.
  on-typed : ∀ {α} {A : ∀ {n} {σ : Type n} -> Term⁽⁾ σ -> Set α}
           -> (f : ∀ {n} {σ : Type n} -> (t : Term⁽⁾ σ) -> A t) -> ∀ e -> _
  on-typed f e =
    runM e                                >>=⊤ proj₂ >>> λ Ψ ->
    let σ = apply Ψ (Var zero) in
    typecheck e (runSubstIn (thickenˢ σ)) >>=⊤ λ t ->
    f (core t)

open import STLC.M.Main using (runM)

on-typed : ∀ {α} {A : ∀ {n} {σ : Type n} -> Term⁽⁾ σ -> Set α}
         -> (f : ∀ {n} {σ : Type n} -> (t : Term⁽⁾ σ) -> A t) -> ∀ e -> _
on-typed f e = runM e >>=⊤ f ∘ thicken ∘ core ∘ proj₂ ∘ proj₂

typed = on-typed $ id
term  = on-typed $ λ t {m Γ}   -> generalize {m} Γ t
term⁻ = on-typed $ λ {n} t {Γ} -> generalize {n} Γ t
normᵖ = on-typed $ pure ∘ erase ∘ norm

module Names {m} where
  name : ∀ n -> Type (suc n + m)
  name = wkᵗ ∘ Var ∘ fromℕ

  a = name 0
  b = name 1
  c = name 2
  d = name 3
  e = name 4
  f = name 5
  g = name 6
  h = name 7
  i = name 8
  j = name 9
  k = name 10
open Names public
