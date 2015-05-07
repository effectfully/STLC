module HMTS.AlgorithmM where

open import Function
open import Relation.Nullary
open import Data.Nat  as Nat
open import Data.Maybe
open import Data.Product
open import Data.List
open import Data.Vec  as Vec hiding (_>>=_)

open import HMTS.Prelude
open import HMTS.Syntax
open import HMTS.Types
open import HMTS.Substitutions

{-# TERMINATING #-}
U : Type -> Type -> Maybe Subst
U (Var i) (Var j)   = just (case i ≟ j of λ
  { (yes _) -> []
  ; (no  _) -> (i , Var j) ∷ []
  })
U (Var i)  τ        = subst i τ
U  σ      (Var j)   = subst j σ
U (σ ⇒ τ) (σ' ⇒ τ') =
  U  σ           σ'          >>= λ Ψ ->
  U (apply Ψ τ) (apply Ψ τ') >>= λ Φ ->
  just (Ψ ∘ˢ Φ)

-- It probably would be nicer to use a coinductive list of fresh names.
-- Wrapped in the State monad or something.
-- Try to typify terms in M instead of afterwards.
M : ∀ {n} -> ℕ -> Con n -> Syntax n -> Type -> Maybe (ℕ × Subst)
M new Γ (varˢ i)  σ =
  _,_ new <$> U σ (Vec.lookup i Γ)
M new Γ (ƛˢ b)   σ =
  U σ (Var new ⇒ Var (next new))                                                     >>= λ Ψ           ->
  M (next (next new)) (Vec.map (apply Ψ) (Var new ∷ Γ)) b (apply Ψ (Var (next new))) >>= λ{ (new' , Φ) ->
  just (new'  , Ψ ∘ˢ Φ)
  }
M new Γ (f · x) σ =
  M (next new)  Γ                    f (Var new ⇒ σ)       >>= λ{ (new'  , Ψ) ->
  M  new'      (Vec.map (apply Ψ) Γ) x (apply Ψ (Var new)) >>= λ{ (new'' , Φ) ->
  just (new'' , Ψ ∘ˢ Φ)
  }}

infer : Syntax⁽⁾ -> Maybe Subst
infer e = proj₂ <$> M 1 [] e (Var 0)
