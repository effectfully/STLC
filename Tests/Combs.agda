module STLC.Tests.Combs where

open import STLC.Main

I : Pure
I = pure (1 # λ x → x)

-- λ {.n} → ƛ var zero
I' : Pure
I' = normᵖ (I · I)

ω : Pure
ω = pure (1 # λ x → x · x)

-- Should we remove this `Lift' or it doesn't matter?
Ωᵀ : Lift ⊤
Ωᵀ = term (ω · ω)

applicator : Term⁽⁾ ((a ⇒ b) ⇒ a ⇒ b)
applicator = term (2 # λ a b → a · b)

applicator⁺ : Term⁺ 2 ((a ⇒ b) ⇒ a ⇒ b)
applicator⁺ = λ {Γ} -> term⁺ (2 # λ a b → a · b) {Γ}

A : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> A -> B
A = eval applicator

gapplicator : ∀ {a b} -> Term ((a ⇒ b) ⇒ a ⇒ b)
gapplicator = wk (generalize applicator)

gapplicator' : {a b : Type 2} -> Term ((a ⇒ b) ⇒ a ⇒ b)
gapplicator' = read _$_

mono-app : {A B : Set} -> (A -> B) -> A -> B
mono-app f x = f x

poly-app : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> A -> B
poly-app = eval (read (inst 2 λ A B -> mono-app {A} {B}))

applicator'' : Term⁽⁾ ((b ⇒ a) ⇒ b ⇒ a)
applicator'' = term (2 # λ a b → a · b)

applicator-speсialized : Term⁽⁾ (((b ⇒ c) ⇒ a) ⇒ (b ⇒ c) ⇒ a)
applicator-speсialized = spec-term 3 (2 # λ a b → a · b)

applicator-generic : ∀ {a b} -> Term⁽⁾ ((a ⇒ b) ⇒ a ⇒ b)
applicator-generic = term (2 # λ a b → a · b)

applicator-generic-specialized : ∀ {a} -> Term⁽⁾ ((a ⇒ a) ⇒ a ⇒ a)
applicator-generic-specialized = applicator-generic

cardinal : Term⁽⁾ ((a ⇒ b ⇒ c) ⇒ b ⇒ a ⇒ c)
cardinal = term (3 # λ a b c → a · c · b)

owl : Term⁽⁾ (((a ⇒ b) ⇒ a) ⇒ (a ⇒ b) ⇒ b)
owl = term (2 # λ a b → b · (a · b))

quacky : Term⁽⁾ (a ⇒ (a ⇒ b) ⇒ (b ⇒ c) ⇒ c)
quacky = term (3 # λ a b c → c · (b · a))

psi : Term⁽⁾ ((b ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ a ⇒ c)
psi = term (4 # λ a b c d → a · (b · c) · (b · d))

phoenix : Term⁽⁾ ((b ⇒ c ⇒ d) ⇒ (a ⇒ b) ⇒ (a ⇒ c) ⇒ a ⇒ d)
phoenix = term (4 # λ a b c d → a · (b · d) · (c · d))

liftM2 : ∀ {α β γ δ} {A : Set α} {B : Set β} {C : Set γ} {D : Set δ}
       -> ((B -> C -> D) -> (A -> B) -> (A -> C) -> A -> D)
liftM2 = eval phoenix

-- eaglebald : Term⁽⁾ ((e ⇒ f ⇒ g) ⇒ (a ⇒ b ⇒ e) ⇒ a ⇒ b ⇒ (c ⇒ d ⇒ f) ⇒ c ⇒ d ⇒ g)
-- eaglebald = term (7 # λ a b c d e f g → a · (b · c · d) · (e · f · g))
