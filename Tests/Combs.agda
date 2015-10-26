module STLC.Tests.Combs where

open import STLC.Main

-- You can omit type signatures.

I : Pure
I = pure (1 # λ x → x)

Iᵀ : ∀ {a} -> Term⁽⁾ (a ⇒ a)
Iᵀ = generalize (core (proj₂ (proj₂ (from-just (infer I))))) -- term I

Iᵀ' : ∀ {α} {A : Set α} -> A -> A
Iᵀ' = eval (term (I · I))

ω : Pure
ω = pure (1 # λ x → x · x)

-- Ωᵀ : _
-- Ωᵀ = term ω

-- Ωᵀ : _
-- Ωᵀ = term (ω · ω)

applicator : _ -- ∀ {a b} -> Term⁽⁾ ((a ⇒ b) ⇒ a ⇒ b)
applicator = term (2 # λ a b → a · b)

A : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> A -> B
A = eval applicator

-- generalize (core (proj₂ (proj₂ (from-just (infer (2 # λ a b → a · b))))))
-- term (2 # λ a b → a · b)

-- applicator' : _ -- Term ((b ⇒ a) ⇒ b ⇒ a)
-- applicator' = term (2 # λ a b → a · b)

-- applicator-speсialized : _ -- Term (((b ⇒ c) ⇒ a) ⇒ (b ⇒ c) ⇒ a)
-- applicator-speсialized = term (2 # λ a b → a · b)

-- applicator-generic : _ -- ∀ {a b} -> Term ((a ⇒ b) ⇒ a ⇒ b)
-- applicator-generic = term (2 # λ a b → a · b)

-- applicator-generic-specialized : _ -- ∀ {a} -> Term ((a ⇒ a) ⇒ a ⇒ a)
-- applicator-generic-specialized = applicator-generic

-- cardinal : _ -- Term ((a ⇒ b ⇒ c) ⇒ b ⇒ a ⇒ c)
-- cardinal = term (3 # λ a b c → a · c · b)

-- owl : _ -- Term (((a ⇒ b) ⇒ a) ⇒ (a ⇒ b) ⇒ b)
-- owl = term (2 # λ a b → b · (a · b))

-- quacky : _ -- Term (a ⇒ (a ⇒ b) ⇒ (b ⇒ c) ⇒ c)
-- quacky = term (3 # λ a b c → c · (b · a))

-- psi : _ -- Term ((b ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ a ⇒ c)
-- psi = term (4 # λ a b c d → a · (b · c) · (b · d))

-- phoenix : ∀ {a b c d} -> Term⁽⁾ ((b ⇒ c ⇒ d) ⇒ (a ⇒ b) ⇒ (a ⇒ c) ⇒ a ⇒ d)
-- phoenix = generalize (core (proj₂ (proj₂ (from-just (infer
--   (4 # λ a b c d → a · (b · d) · (c · d)))))))
-- -- term (4 # λ a b c d → a · (b · d) · (c · d))

-- eaglebald : ∀ {a b c d e f g} -> Term⁽⁾ ((e ⇒ f ⇒ g) ⇒ (a ⇒ b ⇒ e) ⇒ a ⇒ b ⇒ (c ⇒ d ⇒ f) ⇒ c ⇒ d ⇒ g)
-- eaglebald = term (7 # λ a b c d e f g → a · (b · c · d) · (e · f · g))
