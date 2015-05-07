module HMTS.Tests where

open import Data.Unit

open import HMTS.Main

-- You can omit type signatures.

I : Pure
I = pure (1 # λ x → x)

Iᵀ : Term (a ⇒ a)
Iᵀ = term I

Iᵀ' : Term (a ⇒ a)
Iᵀ' = term (I · I)

ω : Pure 
ω = pure (1 # λ x → x · x)

Ωᵀ : ⊤
Ωᵀ = term (ω · ω)

applicator : Term ((a ⇒ b) ⇒ a ⇒ b)
applicator = term (2 # λ a b → a · b)

applicator' : Term ((b ⇒ a) ⇒ b ⇒ a)
applicator' = term (2 # λ a b → a · b)

applicator-spelialized : Term ((a ⇒ a) ⇒ a ⇒ a)
applicator-spelialized = term (2 # λ a b → a · b)

applicator-generic : ∀ {a b} -> Term ((a ⇒ b) ⇒ a ⇒ b)
applicator-generic = term (2 # λ a b → a · b)

applicator-generic-specialized : ∀ {a} -> Term ((a ⇒ a) ⇒ a ⇒ a)
applicator-generic-specialized = applicator-generic

cardinal : Term ((a ⇒ b ⇒ c) ⇒ b ⇒ a ⇒ c)
cardinal = term (3 # λ a b c -> a · c · b)

owl : Term (((a ⇒ b) ⇒ a) ⇒ (a ⇒ b) ⇒ b)
owl = term (2 # λ a b → b · (a · b))

quacky : Term (a ⇒ (a ⇒ b) ⇒ (b ⇒ c) ⇒ c)
quacky = term (3 # λ a b c → c · (b · a))

psi : Term ((b ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ a ⇒ c)
psi = term (4 # λ a b c d → a · (b · c) · (b · d))

phoenix : Term ((b ⇒ c ⇒ d) ⇒ (a ⇒ b) ⇒ (a ⇒ c) ⇒ a ⇒ d)
phoenix = term (4 # λ a b c d → a · (b · d) · (c · d))

eaglebald : Term ((e ⇒ f ⇒ g) ⇒ (a ⇒ b ⇒ e) ⇒ a ⇒ b ⇒ (c ⇒ d ⇒ f) ⇒ c ⇒ d ⇒ g)
eaglebald = term (7 # λ a b c d e f g → a · (b · c · d) · (e · f · g))
