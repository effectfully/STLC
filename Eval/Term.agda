module STLC.Eval.Term where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin
open import Data.Fin.Properties
open import Data.Maybe.Base hiding (map)
open import Data.Maybe using ()
open import Data.Product    hiding (map)
open import Data.List.Base  hiding (unfold)

open import STLC.Utilities.Prelude
open import STLC.Eval.Type
open import STLC.Data.Type renaming (Type to Typeⁿ) hiding (Con; _▻_)
open import STLC.Data.Term renaming (_⊢_ to _⊢ⁿ_; module _⊢_ to _⊢ⁿ_; Term to Termⁿ)

infix  3 _⊢_
infixl 5 _∙_

data _⊢_ {n} (Γ : Con n) : Type n -> Set where
  var : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _∙_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ

Term : ∀ {n} -> Type n -> Set
Term σ = [] ⊢ σ

maybeFin : ∀ {m} -> ℕ -> Maybe (Fin m)
maybeFin {0}      n      = nothing
maybeFin {suc m}  0      = just zero
maybeFin {suc m} (suc n) = suc <$> maybeFin n

eraseᵀ : ∀ {n} -> Type n -> Typeⁿ
eraseᵀ (Var i) = Var (toℕ i)
eraseᵀ (σ ⇒ τ) = eraseᵀ σ ⇒ eraseᵀ τ

unⁿᵀ : ∀ n -> Typeⁿ -> Maybe (Type n)
unⁿᵀ n (Var i) = Var <$> maybeFin i
unⁿᵀ n (σ ⇒ τ) = _⇒_ <$> unⁿᵀ n σ ⊛ unⁿᵀ n τ

maybeFin≡just : ∀ {m n i} -> maybeFin {m} n ≡ just i -> n ≡ toℕ i
maybeFin≡just {0}                     ()
maybeFin≡just {suc m} {0}             refl = refl
maybeFin≡just {suc m} {suc n} {zero}  r    with maybeFin {m} n | r
... | nothing | ()
... | just  _ | ()
maybeFin≡just {suc m} {suc n} {suc i} r    with maybeFin {m} n | inspect (maybeFin {m}) n | r
... | nothing |  _    | ()
... | just  _ | [ s ] | r'                 with i | r'
... | ._ | refl                            = cong suc (maybeFin≡just s)

unfold : ∀ {n σ'} σ -> unⁿᵀ n σ ≡ just σ' -> σ ≡ eraseᵀ σ'
unfold {n} {Var i' } (Var i) r with maybeFin {n} i | inspect (maybeFin {n}) i | r
... | nothing |  _    | ()
... | just  k | [ s ] | r'     with k | r'
... | ._ | refl                = cong Var (maybeFin≡just s)
unfold {n} {σ' ⇒ τ'} (Var i) r with maybeFin {n} i | r
... | nothing | ()
... | just _  | ()
unfold {n} {Var i' } (σ ⇒ τ) r with unⁿᵀ n σ | unⁿᵀ n τ | r
... | nothing | _       | ()
... | just  _ | nothing | ()
... | just  _ | just  _ | ()
unfold {n} {σ' ⇒ τ'} (σ ⇒ τ) r with unⁿᵀ n σ | unⁿᵀ n τ | inspect (unⁿᵀ n) σ | inspect (unⁿᵀ n) τ | r
... | nothing | _       |  _    |  _    | ()
... | just  _ | nothing |  _    |  _    | ()
... | just  _ | just  _ | [ s ] | [ t ] | r' with σ' | τ' | r'
... | ._ | ._ | refl           = cong₂ _⇒_ (unfold σ s) (unfold τ t)

coerce : ∀ {n Γ} {σ τ : Type n} -> σ ≡ τ -> Γ ⊢ σ -> Γ ⊢ τ
coerce refl = id

uneraseᵀ : ∀ {n} {σ τ : Type n} -> eraseᵀ σ ≡ eraseᵀ τ -> σ ≡ τ
uneraseᵀ {σ = Var i} {Var i' } r  = cong Var (toℕ-injective (Var-inj r))
uneraseᵀ {σ = Var _} {_  ⇒ _ } ()
uneraseᵀ {σ = σ ⇒ τ} {Var _  } ()
uneraseᵀ {σ = σ ⇒ τ} {σ' ⇒ τ'} r  =
  cong₂ _⇒_ (uneraseᵀ (proj₁ (⇒-inj r))) (uneraseᵀ (proj₂ (⇒-inj r)))

unerase-in : ∀ {n σ Γ Γ'} {σ' : Type n}
           -> Γ ≡ map eraseᵀ Γ' -> σ ≡ eraseᵀ σ' -> σ ∈ Γ -> σ' ∈ Γ'
unerase-in {Γ' = []}    ()   q     vz
unerase-in {Γ' = _ ∷ _} refl q     vz    rewrite uneraseᵀ q = vz
unerase-in {Γ' = []}    ()   q    (vs v)
unerase-in {Γ' = _ ∷ _} refl refl (vs v) = vs (unerase-in refl refl v)

unⁿ-go : ∀ {n σ Γ Γ'} {σ' : Type n}
       -> Γ ⊢ⁿ σ -> Γ ≡ map eraseᵀ Γ' -> σ ≡ eraseᵀ σ' -> Maybe (Γ' ⊢ σ')
unⁿ-go              (var v)       p    q    = just (var (unerase-in p q v))
unⁿ-go {σ' = Var _} (ƛ b)         p    ()
unⁿ-go {σ' = _ ⇒ _} (ƛ b)         refl refl = ƛ_ <$> unⁿ-go b refl refl
unⁿ-go {n}          (_∙_ {σ} f x) p    q    with unⁿᵀ n σ | inspect (unⁿᵀ n) σ
... | nothing |  _                          = nothing
... | just σ' | [ r ]                       =
  _∙_ <$> unⁿ-go f p (cong₂ _⇒_ (unfold σ r) q) ⊛ unⁿ-go x p (unfold σ r)

max : Typeⁿ -> ℕ
max (Var i) = i
max (σ ⇒ τ) = max σ ⊔ max τ

unⁿ : ∀ {σ} -> Termⁿ σ -> unⁿᵀ (suc (max σ)) σ >>=ᵀᵂ λ σ' -> Maybe (Term σ')
unⁿ {σ} x = tag (unⁿᵀ (suc (max σ)) σ >>=⊤ᴾ λ p -> unⁿ-go x refl (unfold σ p))
