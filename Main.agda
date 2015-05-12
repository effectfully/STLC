module HMTS.Main where

open import Function
open import Data.Product

open import HMTS.Utilities.Generalize
open import HMTS.AlgorithmM.Main
open import HMTS.NbE.Main          as M
open import HMTS.NbE.LiftableTerms as L

open import Data.Unit.Base         public using  (⊤)
open import Data.Nat.Base          public hiding (erase)
open import HMTS.Utilities.Prelude public
open import HMTS.Utilities.Bind    public
open import HMTS.Utilities.Names   public
open import HMTS.Data.Syntax       public
open import HMTS.Data.Type         public
open import HMTS.Data.Term         public

run : ∀ {γ} {C : ∀ {Γ σ} -> (e : Γ ⊢ σ) -> Set γ}
    -> (∀ {Γ σ} -> (e : Γ ⊢ σ) -> C e)
    -> (eˢ : Syntax⁽⁾)
    -> runM eˢ >>=ᵀ λ{ (_ , e) -> C (unᵛ e) }
run f eˢ =
       runM eˢ >>=⊤ λ{ (_ , e) -> f (unᵛ e) }

term  = run  generalize
norm  = run (erase ∘ M.normalize)
norm' = run (erase ∘ L.normalize)
