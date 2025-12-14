import Mathlib

def Implies (p q : Prop) : Prop := p → q

#check And
#check Or
#check Not
#check Implies

variable (p q r : Prop)
#check p
#check Not p
#check Or p (Not p)

#check And p q
#check Or (And p q) r
#check Implies (And p q) (And q p)

structure Proof (p : Prop) : Type where
  proof : p

#check Proof

axiom and_commut (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)

#check and_commut p q

axiom modus_ponens (p q : Prop) :
  Proof (Implies p q) → Proof p →
  Proof q

axiom implies_intro (p q : Prop) :
  (Proof p → Proof q) → Proof (Implies p q)

--

set_option linter.unusedVariables false

variable {p : Prop}
variable {q : Prop}

theorem t0 : p → p := fun p : p => p
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
theorem t1_1 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp

#print t0
#print t1
#print t1_1

axiom unsound : False
axiom Falsity : 1 = 0

-- Everything follows from false
theorem falsehood : 1 = 0 :=
  False.elim unsound

theorem falsehood2 : 1 = 0 :=
  Falsity

theorem falsehood3 : 3 = 0 :=
  False.elim unsound

#print falsehood
#print falsehood2


variable (p q r s : Prop)

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)

theorem t3 (h₁ : p → r) (h₂ : r → s) : p → s :=
  fun h₃ : p =>
  show s from h₂ (h₁ h₃)

theorem t4 (h₁ : p → q → r) (h₂ : r → s) (h₃ : q) : p → s :=
  fun h₄ : p =>
  show s from h₂ (h₁ h₄ h₃)

theorem t5 (h₁ : p → q → r → s) (h₂ : q) (h₃ : r) : p → s :=
  fun h₄ : p =>
  show s from h₁ h₄ h₂ h₃

--

variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

--

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)
