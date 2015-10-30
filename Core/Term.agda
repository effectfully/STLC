module STLC.Core.Term where

open import STLC.Lib.Prelude
open import STLC.Core.Syntax
open import STLC.Core.Type

infixl 5 _▻_
infix  4 _∈_ _⊆_ _⊢_ _⊂[_]_
infixr 3 ƛ_
infixl 6 _·_

data Con n : Set where
  ε   : Con n
  _▻_ : Con n -> Type n -> Con n

data _⊂[_]_ {n} Γ σ : Con n -> Set where
  vtop  :            Γ ⊂[ σ ] Γ ▻ σ
  vskip : ∀ {Δ τ} -> Γ ⊂[ σ ] Δ     -> Γ ⊂[ σ ] Δ ▻ τ

data _⊆_ {n} : Con n -> Con n -> Set where
  stop : ∀ {Γ}     -> Γ ⊆ Γ
  skip : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ     ⊆ Δ ▻ σ
  keep : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ▻ σ ⊆ Δ ▻ σ

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

Links : Set₁
Links = ∀ {n} -> Con n -> Type n -> Set

_∋_ : Links
_∋_ = flip _∈_

Renames : Links -> Set
Renames _∙_ = ∀ {n σ} {Γ Δ : Con n} -> Γ ⊆ Δ -> Γ ∙ σ -> Δ ∙ σ

_∸>_ : Links -> Links -> Set
_∙_ ∸> _◆_ = ∀ {n σ} {Γ : Con n} -> Γ ∙ σ -> Γ ◆ σ

foldrᶜ : ∀ {α n} {A : Set α} -> (Type n -> A -> A) -> A -> Con n -> A
foldrᶜ f z  ε      = z
foldrᶜ f z (Γ ▻ σ) = f σ (foldrᶜ f z Γ)

mapᶜ : ∀ {n m} -> (Type n -> Type m) -> Con n -> Con m
mapᶜ f = foldrᶜ (λ σ Γ -> Γ ▻ f σ) ε

lenᶜ : ∀ {n} -> Con n -> ℕ
lenᶜ = foldrᶜ (const suc) 0

top : ∀ {n σ} {Γ : Con n} -> Γ ⊆ Γ ▻ σ
top = skip stop

full : ∀ {n} {Γ : Con n} -> ε ⊆ Γ
full {Γ = ε}     = stop
full {Γ = Γ ▻ σ} = skip full

_∘ˢ_ : ∀ {n} {Γ Δ Ξ : Con n} -> Δ ⊆ Ξ -> Γ ⊆ Δ -> Γ ⊆ Ξ
stop   ∘ˢ ι      = ι
skip κ ∘ˢ ι      = skip (κ ∘ˢ ι)
keep κ ∘ˢ stop   = keep κ
keep κ ∘ˢ skip ι = skip (κ ∘ˢ ι)
keep κ ∘ˢ keep ι = keep (κ ∘ˢ ι)

⊂[]-to-∈ : ∀ {n σ} {Γ Δ : Con n} -> Γ ⊂[ σ ] Δ -> σ ∈ Δ
⊂[]-to-∈  vtop     = vz
⊂[]-to-∈ (vskip p) = vs (⊂[]-to-∈ p)

∈-to-Fin : ∀ {n σ} {Γ : Con n} -> σ ∈ Γ -> Fin (lenᶜ Γ)
∈-to-Fin  vz    = zero
∈-to-Fin (vs v) = suc (∈-to-Fin v)

renᵛ : Renames _∋_
renᵛ  stop     v     = v
renᵛ (skip ι)  v     = vs (renᵛ ι v)
renᵛ (keep ι)  vz    = vz
renᵛ (keep ι) (vs v) = vs (renᵛ ι v)

erase : ∀ {n σ} {Γ : Con n} -> Γ ⊢ σ -> Syntax (lenᶜ Γ)
erase (var v) = var (∈-to-Fin v)
erase (ƛ b)   = ƛ (erase b)
erase (f · x) = erase f · erase x

ren : Renames _⊢_
ren ι (var v) = var (renᵛ ι v)
ren ι (ƛ b)   = ƛ (ren (keep ι) b)
ren ι (f · x) = ren ι f · ren ι x

term : ∀ {n} {σ : Type n} -> Term⁽⁾ σ -> Term σ
term t = ren full t

specializeᵛ : ∀ {n m σ} {Γ : Con n}
            -> (Ψ : Subst n m) -> σ ∈ Γ -> apply Ψ σ ∈ mapᶜ (apply Ψ) Γ
specializeᵛ Ψ  vz    = vz
specializeᵛ Ψ (vs v) = vs (specializeᵛ Ψ v)

specialize : ∀ {n m σ} {Γ : Con n}
           -> (Ψ : Subst n m) -> Γ ⊢ σ -> mapᶜ (apply Ψ) Γ ⊢ apply Ψ σ
specialize Ψ (var v) = var (specializeᵛ Ψ v)
specialize Ψ (ƛ b)   = ƛ (specialize Ψ b)
specialize Ψ (f · x) = specialize Ψ f · specialize Ψ x

generalize : ∀ {n σ} {Γ : Con n}
           -> Γ ⊢ σ -> Associate (ftv σ) Var λ Ψ -> mapᶜ (apply Ψ) Γ ⊢ apply Ψ σ
generalize {σ = σ} = go (ftv σ) where
  go : ∀ {n Γ σ} {c : Subst n n -> Subst n n} is
     -> Γ ⊢ σ -> Associate is Var λ Ψ -> let Φ = c Ψ in mapᶜ (apply Φ) Γ ⊢ apply Φ σ
  go  []      t = specialize _ t
  go (i ∷ is) t = go is t

thicken : ∀ {n σ} {Γ : Con n} -> Γ ⊢ σ -> _
thicken {σ = σ} = specialize λ i ->
  maybe Var undefined (lookup-for i (map swap (enumerate (ftv σ))))
    where postulate undefined : _
