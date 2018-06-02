module STLC.M.Term where

open import STLC.Lib.Prelude
open import STLC.Type
import STLC.Term as C

infixl 5 _▻_
infix  4 _∈_ _⊢_
infixr 3 ƛ_
infixl 6 _·_

data Con n : ℕ -> Set where
  ε   : Con n 0
  _▻_ : ∀ {l} -> Con n l -> Type n -> Con n (suc l)

data _∈_ {n} σ : ∀ {l} -> Con n l -> Set where
  vz : ∀ {l}   {Γ : Con n l} -> σ ∈ Γ ▻ σ
  vs : ∀ {l τ} {Γ : Con n l} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ

data _⊢_ {n l} (Γ : Con n l) : Type n -> Set where
  var : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ

coreᶜ : ∀ {n l} -> (Γ : Con n l) -> C.Con n
coreᶜ  ε      = C.ε
coreᶜ (Γ ▻ σ) = coreᶜ Γ C.▻ σ

coreᵛ : ∀ {n l σ} {Γ : Con n l} -> σ ∈ Γ -> σ C.∈ coreᶜ Γ
coreᵛ  vz    = C.vz
coreᵛ (vs v) = C.vs (coreᵛ v)

core : ∀ {n l σ} {Γ : Con n l} -> Γ ⊢ σ -> coreᶜ Γ C.⊢ σ
core (var v) = C.var (coreᵛ v)
core (ƛ b)   = C.ƛ (core b)
core (f · x) = core f C.· core x

lookupᶜ : ∀ {n l} -> Fin l -> Con n l -> Type n
lookupᶜ  zero   (Γ ▻ σ) = σ
lookupᶜ (suc i) (Γ ▻ σ) = lookupᶜ i Γ

mapᶜ : ∀ {n m l} -> (Type n -> Type m) -> Con n l -> Con m l
mapᶜ f  ε      = ε
mapᶜ f (Γ ▻ σ) = mapᶜ f Γ ▻ f σ

lookupᶜ-∈ : ∀ {n l} i -> (Γ : Con n l) -> lookupᶜ i Γ ∈ Γ
lookupᶜ-∈  zero   (Γ ▻ σ) = vz
lookupᶜ-∈ (suc i) (Γ ▻ σ) = vs (lookupᶜ-∈ i Γ)

coerceBy : ∀ {n l σ τ} {Γ : Con n l} -> σ ≡ τ -> Γ ⊢ σ -> Γ ⊢ τ
coerceBy refl = id

coerce : ∀ {n l σ τ} {Γ : Con n l} -> Γ ⊢ σ -> Maybe (Γ ⊢ τ)
coerce {σ = σ} {τ} t = flip coerceBy t <$> decToMaybe (σ ≟ τ)

specializeᵛ : ∀ {n m l σ} {Γ : Con n l}
            -> (Ψ : Subst n m) -> σ ∈ Γ -> apply Ψ σ ∈ mapᶜ (apply Ψ) Γ
specializeᵛ Ψ  vz    = vz
specializeᵛ Ψ (vs v) = vs (specializeᵛ Ψ v)

specialize : ∀ {n m l σ} {Γ : Con n l}
           -> (Ψ : Subst n m) -> Γ ⊢ σ -> mapᶜ (apply Ψ) Γ ⊢ apply Ψ σ
specialize Ψ (var v) = var (specializeᵛ Ψ v)
specialize Ψ (ƛ b)   = ƛ (specialize Ψ b)
specialize Ψ (f · x) = specialize Ψ f · specialize Ψ x

mapᶜ-mapᶜ : ∀ {n m p l} {g : Type m -> Type p} {f : Type n -> Type m} (Γ : Con n l)
          -> mapᶜ g (mapᶜ f Γ) ≡ mapᶜ (g ∘ f) Γ
mapᶜ-mapᶜ  ε      = refl
mapᶜ-mapᶜ (Γ ▻ σ) = cong (_▻ _) (mapᶜ-mapᶜ Γ)
