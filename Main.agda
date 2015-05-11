module HMTS.Main where

open import Function
open import Data.Product

open import Data.Unit                 public using  (⊤)
open import Data.Nat                  public hiding (erase)

open import HMTS.Utilities.Prelude    public
open import HMTS.Utilities.Bind       public
open import HMTS.Utilities.Generalize public
open import HMTS.Utilities.Names      public
open import HMTS.Data.Syntax          public
open import HMTS.Data.Type            public
open import HMTS.Data.Term            public
open import HMTS.AlgorithmM.Main      public
open import HMTS.NbE.Main             public

run : ∀ {γ} {C : ∀ {Γ σ} -> (e : Γ ⊢ σ) -> Set γ}
    -> (∀ {Γ σ} -> (e : Γ ⊢ σ) -> C e)
    -> (eˢ : Syntax⁽⁾)
    -> runM eˢ >>=ᵀ λ{ (_ , e) -> C (unᵛ e) }
run f eˢ =
       runM eˢ >>=⊤ λ{ (_ , e) -> f (unᵛ e) }

term = run  generalize

norm = run (erase ∘ normalize)
