module HMTS.AlgorithmM where

open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Data.Empty
open import Data.Nat  as Nat
open import Data.Maybe
open import Data.Product
open import Data.Vec  as Vec hiding (_>>=_)

open import HMTS.Prelude
open import HMTS.Syntax
open import HMTS.Types
open import HMTS.Substitutions
open import HMTS.Terms
open import HMTS.Alpha using (alpha)

subst : ∀ i τ -> Maybe (∃ λ Ψ -> apply Ψ (Var i) ≡ apply Ψ τ)
subst i σ = case i ∈? ftv-all σ of λ
  { (yes _) -> nothing
  ; (no  p) -> just (leaf (just (i , σ)) , subst-apply i σ p)
  }

{-# TERMINATING #-}
U : ∀ σ τ -> Maybe (∃ λ Ψ -> apply Ψ σ ≡ apply Ψ τ)
U (Var i) (Var j)   = case i ≟ j of λ
  { (yes p) -> just (leaf nothing , cong Var p)
  ; (no  _) -> subst i (Var j)
  }
U (Var i)  τ        = subst i τ
U  σ      (Var j)   = subst j σ >>= λ{ (Ψ , p) -> just (Ψ , sym p) }
U (σ ⇒ τ) (σ' ⇒ τ') =
  U  σ           σ'          >>= λ{ (Ψ , p) ->
  U (apply Ψ τ) (apply Ψ τ') >>= λ{ (Φ , q) ->
  just (branch Φ Ψ , compose Φ Ψ p q)
  }}

lam : ∀ {new n σ} {Γ : Con n} Φ Ψ
    -> apply Ψ σ ≡ apply Ψ (Var new ⇒ Var (next new))
    -> map-apply Φ (map-apply Ψ (Γ ▻ Var new)) ⊢ apply Φ (apply Ψ (Var (next new)))
    -> map-apply Φ (map-apply Ψ Γ) ⊢ apply Φ (apply Ψ σ)
lam {new} {Γ = Γ} Φ Ψ p b
  rewrite ▻-expand² Φ Ψ Γ (Var new)
  | p |   ⇒-expand² Φ Ψ (Var new) (Var (suc new)) = ƛ b

M : ∀ {n} -> ℕ -> (Γ : Con n) -> Syntax n -> (σ : Type)
  -> Maybe (ℕ × ∃ λ Ψ -> map-apply Ψ Γ ⊢ apply Ψ σ)
M new Γ (varˢ i)  σ =
  U σ (Vec.lookup i Γ) >>= λ{ (Ψ , p) ->
  just (new , Ψ , coerceBy (sym p) (specialize Ψ (var (lookup-in i Γ))))
  }
M new Γ (ƛˢ bˢ)   σ =
  U σ (Var new ⇒ Var (next new))                                                >>= λ{ (Ψ , p)        ->
  M (next (next new)) (map-apply Ψ (Var new ∷ Γ)) bˢ (apply Ψ (Var (next new))) >>= λ{ (new' , Φ , b) ->
  just (new' , branch Φ Ψ , lam Φ Ψ p b)
  }}
M new Γ (fˢ · xˢ) σ =
  M (next new)  Γ              fˢ (Var new ⇒ σ)       >>= λ{ (new'  , Ψ , f) ->
  M  new'      (map-apply Ψ Γ) xˢ (apply Ψ (Var new)) >>= λ{ (new'' , Φ , x) ->
  just (new'' , branch Φ Ψ , coerceBy (⇒-expand² Φ Ψ (Var new) σ) (specialize Φ f) ∙ x)
  }}

term = λ eˢ -> M 1 [] eˢ (Var 0) >>=⊤ λ{ (_ , _ , e) -> alpha e }
