module STLC.Tests.Eval where

open import Function
open import Relation.Binary.PropositionalEquality

open import STLC.Main

Applicator : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> A -> B
Applicator = eval (compile (2 # λ a b → a · b))

quacky : Syntax⁽⁾
quacky = 3 # λ a b c → c · (b · a)

Quacky : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
       -> A -> (A -> B) -> (B -> C) -> C
Quacky = eval (compile quacky)

-- Nope, too many computations.

-- Psi : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
--     -> (B -> B -> C) -> (A -> B) -> A -> A -> C
-- Psi = eval (compile (4 # λ a b c d → a · (b · c) · (b · d)))
