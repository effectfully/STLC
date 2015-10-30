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
Ωᵀ = typify (ω · ω)

applicator : Term⁽⁾ ((Var zero ⇒ Var (suc zero)) ⇒ Var zero ⇒ Var (suc zero))
applicator = typify (2 # λ a b → a · b)

applicator' : Term⁽⁾ ((Var zero ⇒ Var (suc (zero {0}))) ⇒ Var zero ⇒ Var (suc zero))
applicator' = read _$_

A : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> A -> B
A = eval applicator

gapplicator : ∀ {a b} -> Term ((a ⇒ b) ⇒ a ⇒ b)
gapplicator = term (generalize applicator)

mono-app : {A B : Set} -> (A -> B) -> A -> B
mono-app f x = f x

poly-app : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> A -> B
poly-app = eval (read (inst 2 λ A B -> mono-app {A} {B}))

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
-- eaglebald = generalize (term (7 # λ a b c d e f g → a · (b · c · d) · (e · f · g)))
