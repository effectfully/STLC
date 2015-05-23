module STLC.AlgorithmM.Main where

open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Data.Empty
open import Data.Nat.Base
open import Data.Maybe.Base
open import Data.Product
open import Data.Vec  as Vec hiding (_>>=_)

open import STLC.Utilities.Prelude
open import STLC.Data.Syntax
open import STLC.Data.Type
open import STLC.AlgorithmM.Substitution
open import STLC.AlgorithmM.Term

subst : ∀ i τ -> Maybe (∃ λ Ψ -> apply Ψ (Var i) ≡ apply Ψ τ)
subst i σ = case i ∈? ftv-all σ of λ
  { (yes _) -> nothing
  ; (no  p) -> just (leaf (just (i , σ)) , subst-apply i σ p)
  }

-- Yep, Conor McBride's unification.
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

lam : ∀ {new n σ} {Γ : Conᵛ n} Φ Ψ
    -> apply Ψ σ ≡ apply Ψ (Var new ⇒ Var (next new))
    -> map-apply Φ (map-apply Ψ (Γ ▻ᵛ Var new)) ⊢ apply Φ (apply Ψ (Var (next new)))
    -> map-apply Φ (map-apply Ψ Γ) ⊢ apply Φ (apply Ψ σ)
lam {new} {Γ = Γ} Φ Ψ p b rewrite ▻ᵛ-expand² Φ Ψ Γ (Var new) =
  coerceBy
    (trans (sym (⇒-expand² Φ Ψ (Var new) (Var (next new))))
           (sym (cong (apply Φ) p)))
    (ƛ b)

M : ∀ {n} -> ℕ -> (Γ : Conᵛ n) -> (x : Syntax n) -> (σ : Type)
  -> Maybe (ℕ × ∃ λ Ψ -> map-apply Ψ Γ ⊢ apply Ψ σ)
M new Γ (varˢ i)  σ =
  U σ (Vec.lookup i Γ)
    >>= λ{ (Ψ , p) ->
  just (new , Ψ , coerceBy (sym p) (Ψ # var (lookup-in i Γ)))
  }
M new Γ (ƛˢ bˢ)   σ =
  U σ (Var new ⇒ Var (next new))
    >>= λ{ (Ψ , p)        ->
  M (next (next new)) (map-apply Ψ (Γ ▻ᵛ Var new)) bˢ (apply Ψ (Var (next new)))
    >>= λ{ (new' , Φ , b) ->
  just (new' , branch Φ Ψ , lam Φ Ψ p b)
  }}
M new Γ (fˢ · xˢ) σ =
  M (next new)  Γ              fˢ (Var new ⇒ σ)
    >>= λ{ (new'  , Ψ , f) ->
  M  new'      (map-apply Ψ Γ) xˢ (apply Ψ (Var new))
    >>= λ{ (new'' , Φ , x) ->
  just (new'' , branch Φ Ψ , coerceBy (⇒-expand² Φ Ψ (Var new) σ) (Φ # f) ∙ x)
  }}

runM : Syntax⁽⁾ -> Maybe (∃ λ Ψ -> map-apply Ψ [] ⊢ apply Ψ (Var 0))
runM eˢ = proj₂ <$> M 1 [] eˢ (Var 0)
