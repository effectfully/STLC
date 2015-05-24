module STLC.Main where

open import Function
open import Data.Product

open import STLC.Utilities.Generalize
open import STLC.AlgorithmM.Main
open import STLC.AlgorithmM.Term using (unᵛ)
open import STLC.NbE.Main          as M
open import STLC.NbE.LiftableTerms as L
open import STLC.Eval.Term renaming (_⊢_ to _⊢ᶠ_)
open import STLC.Eval.Main

open import Data.Unit.Base         public using  (⊤)
open import Data.Nat.Base          public hiding (erase)
open import STLC.Utilities.Prelude public
open import STLC.Utilities.Bind    public
open import STLC.Utilities.Names   public
open import STLC.Data.Syntax       public
open import STLC.Data.Type         public
open import STLC.Data.Term         public

run : ∀ {γ} {C : ∀ {Γ σ} -> (e : Γ ⊢ σ) -> Set γ}
    -> (∀ {Γ σ} -> (e : Γ ⊢ σ) -> C e)
    -> (eˢ : Syntax⁽⁾)
    -> runM eˢ >>=ᵀ λ{ (_ , e) -> C (unʳ (unᵛ e)) }
run f eˢ =
       runM eˢ >>=⊤ λ{ (_ , e) -> f (unʳ (unᵛ e)) }

term    = run  generalize
norm    = run (erase ∘ M.normalize)
norm'   = run (erase ∘ L.normalize)

compile = λ eˢ ->
  runM eˢ                     >>=⊤ λ{ (_ , e) ->
  unⁿ (thicken (unʳ (unᵛ e))) >>=ʷ λ y ->
  y                           >>=⊤ λ x -> x
  }
eval    = evaluate
