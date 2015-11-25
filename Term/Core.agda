module STLC.Term.Core where

open import STLC.Lib.Prelude
open import STLC.Term.Syntax
open import STLC.Context

infix  4 _∈_ _∋_ _⊢_
infix  3 vs_
infixr 3 ƛ_
infixl 6 _·_

data _∈_ {n} σ : Con n -> Set where
  vz  : ∀ {Γ}   -> σ ∈ Γ ▻ σ
  vs_ : ∀ {Γ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ 

data _⊢_ {n} Γ : Type n -> Set where
  var : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ

Term⁽⁾ : ∀ {n} -> Type n -> Set
Term⁽⁾ σ = ε ⊢ σ

Term : ∀ {n} -> Type n -> Set
Term σ = ∀ {Γ} -> Γ ⊢ σ

Term⁺ : ∀ n -> (∀ {m} -> Type (n + m)) -> Set
Term⁺ n σ = ∀ {m Γ} -> Γ ⊢ σ {m}

_∋_ : Links
_∋_ = flip _∈_

⊂[]-to-∈ : ∀ {n σ} {Γ Δ : Con n} -> Γ ⊂[ σ ] Δ -> σ ∈ Δ
⊂[]-to-∈  vtop     = vz
⊂[]-to-∈ (vskip p) = vs (⊂[]-to-∈ p)

∈-to-Fin : ∀ {n σ} {Γ : Con n} -> σ ∈ Γ -> Fin (lenᶜ Γ)
∈-to-Fin  vz    = zero
∈-to-Fin (vs v) = suc (∈-to-Fin v)

wkᵛ : ∀ {n σ} {Δ Γ : Con n} -> σ ∈ Γ -> σ ∈ Δ ▻▻ Γ
wkᵛ  vz    = vz
wkᵛ (vs v) = vs (wkᵛ v)

renᵛ : Renames _∋_
renᵛ  stop     v     = v
renᵛ (skip ι)  v     = vs (renᵛ ι v)
renᵛ (keep ι)  vz    = vz
renᵛ (keep ι) (vs v) = vs (renᵛ ι v)

erase : ∀ {n σ} {Γ : Con n} -> Γ ⊢ σ -> Syntax (lenᶜ Γ)
erase (var v) = var (∈-to-Fin v)
erase (ƛ b)   = ƛ (erase b)
erase (f · x) = erase f · erase x

upper : ∀ {n σ} {Γ : Con n} -> Γ ⊢ σ -> ℕ
upper {n} _ = n

wk : ∀ {n σ} {Δ Γ : Con n} -> Γ ⊢ σ -> Δ ▻▻ Γ ⊢ σ
wk (var v) = var (wkᵛ v)
wk (ƛ b)   = ƛ (wk b)
wk (f · x) = wk f · wk x

ren : Renames _⊢_
ren ι (var v) = var (renᵛ ι v)
ren ι (ƛ b)   = ƛ (ren (keep ι) b)
ren ι (f · x) = ren ι f · ren ι x

specializeᵛ : ∀ {n m σ} {Γ : Con n} -> (Ψ : Subst n m) -> σ ∈ Γ -> apply Ψ σ ∈ mapᶜ (apply Ψ) Γ
specializeᵛ Ψ  vz    = vz
specializeᵛ Ψ (vs v) = vs (specializeᵛ Ψ v)

specialize : ∀ {n m σ} {Γ : Con n} -> (Ψ : Subst n m) -> Γ ⊢ σ -> mapᶜ (apply Ψ) Γ ⊢ apply Ψ σ
specialize Ψ (var v) = var (specializeᵛ Ψ v)
specialize Ψ (ƛ b)   = ƛ (specialize Ψ b)
specialize Ψ (f · x) = specialize Ψ f · specialize Ψ x

widen : ∀ {n σ} {Γ : Con n} m -> Γ ⊢ σ -> _
widen m = specialize (wkᵗ {m} ∘ Var)

-- These two are far slower than they were.
thicken : ∀ {n σ} {Γ : Con n} -> Γ ⊢ σ -> _
thicken {σ = σ} = specialize (unsafeToSubst (thickenˢ σ))

generalize : ∀ {m n} {σ : Type n}
           -> (Γ : Con m) -> Term⁽⁾ σ ->
                 Associate (ftv σ) λ (Ψ : SubstInFtv σ m) ->
                    Γ ⊢ apply (unsafeToSubst (fromInFtv σ Ψ)) σ
generalize {σ = σ} _ t = associate (ftv σ) λ Ψ -> wk (specialize (unsafeToSubst (fromInFtv σ Ψ)) t)

-- data SubstsIn {n} : Con n -> ℕ -> Set where
--   øˢ   : ∀ {m} -> SubstsIn ε m
--   _▷ˢ_ : ∀ {m Γ σ} -> SubstsIn Γ m -> SubstIn σ m -> SubstsIn (Γ ▻ σ) m

-- runSubstsIn : ∀ {n m} {Γ : Con n} -> SubstsIn Γ m -> Con m
-- runSubstsIn  øˢ      = ε
-- runSubstsIn (ρ ▷ˢ Ψ) = runSubstsIn ρ ▻ runSubstIn Ψ

-- Yeah.
-- specialize⁽⁾ : ∀ {n m σ} {Γ : Con n}
--              -> (ρ : SubstsIn Γ m) -> (Ψ : SubstIn σ m) -> Γ ⊢ σ -> runSubstsIn ρ ⊢ runSubstIn Ψ
-- specialize⁽⁾ ρ Ψ (var v) = {!!}
-- specialize⁽⁾ ρ Ψ (ƛ b)   = ƛ (specialize⁽⁾ (ρ ▷ˢ (Ψ ∘ vl)) (Ψ ∘ vr) b)
-- specialize⁽⁾ ρ Ψ (f · x) = specialize⁽⁾ ρ {!!} f · specialize⁽⁾ ρ {!!} x
