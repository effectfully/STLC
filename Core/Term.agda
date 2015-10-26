module STLC.Core.Term where

open import STLC.Lib.Prelude
open import STLC.Core.Syntax
open import STLC.Core.Type

infixl 5 _▻_
infix  4 _∈_ _⊢_
infixr 3 ƛ_
infixl 6 _·_

data Con n : Set where
  ε   : Con n
  _▻_ : Con n -> Type n -> Con n

data _∈_ {n} σ : Con n -> Set where
  vz : ∀ {Γ}   -> σ ∈ Γ ▻ σ
  vs : ∀ {Γ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ 

data _⊢_ {n} Γ : Type n -> Set where
  var : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ

Term⁽⁾ : ∀ {n} -> Type n -> Set
Term⁽⁾ σ = ε ⊢ σ

Term : ∀ {n} -> Type n -> Set
Term σ = ∀ {Γ} -> Γ ⊢ σ

mapᶜ : ∀ {n m} -> (Type n -> Type m) -> Con n -> Con m
mapᶜ f  ε      = ε
mapᶜ f (Γ ▻ σ) = mapᶜ f Γ ▻ f σ

lenᶜ : ∀ {n} -> Con n -> ℕ
lenᶜ  ε      = 0
lenᶜ (Γ ▻ σ) = suc (lenᶜ Γ)

∈-to-Fin : ∀ {n σ} {Γ : Con n} -> σ ∈ Γ -> Fin (lenᶜ Γ)
∈-to-Fin  vz    = zero
∈-to-Fin (vs v) = suc (∈-to-Fin v)

erase : ∀ {n σ} {Γ : Con n} -> Γ ⊢ σ -> Syntax (lenᶜ Γ)
erase (var v) = var (∈-to-Fin v)
erase (ƛ b)   = ƛ (erase b)
erase (f · x) = erase f · erase x

specializeᵛ : ∀ {n m σ} {Γ : Con n}
            -> (Ψ : Subst n m) -> σ ∈ Γ -> apply Ψ σ ∈ mapᶜ (apply Ψ) Γ
specializeᵛ Ψ  vz    = vz
specializeᵛ Ψ (vs v) = vs (specializeᵛ Ψ v)

specialize : ∀ {n m σ} {Γ : Con n}
           -> (Ψ : Subst n m) -> Γ ⊢ σ -> mapᶜ (apply Ψ) Γ ⊢ apply Ψ σ
specialize Ψ (var v) = var (specializeᵛ Ψ v)
specialize Ψ (ƛ b)   = ƛ (specialize Ψ b)
specialize Ψ (f · x) = specialize Ψ f · specialize Ψ x

generalizeᶜ : ∀ {n Γ σ} {c : Subst n n -> Subst n n} is
            -> Γ ⊢ σ -> Associate is Var λ Ψ -> let Φ = c Ψ in mapᶜ (apply Φ) Γ ⊢ apply Φ σ
generalizeᶜ  []      t = specialize _ t
generalizeᶜ (i ∷ is) t = generalizeᶜ is t

generalize : ∀ {n σ} {Γ : Con n}
           -> Γ ⊢ σ -> Associate (ftv σ) Var λ Ψ -> mapᶜ (apply Ψ) Γ ⊢ apply Ψ σ
generalize {σ = σ} = generalizeᶜ (ftv σ)

thicken : ∀ {n σ} {Γ : Con n} -> Γ ⊢ σ -> _
thicken {σ = σ} = specialize λ i ->
  maybe Var undefined (lookup-for i (map swap (enumerate (ftv σ))))
    where postulate undefined : _
