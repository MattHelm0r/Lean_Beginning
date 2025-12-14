-- https://leanprover.github.io/theorem_proving_in_lean4/

import Mathlib

/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1

-- "&&" is the Boolean and
#check b1 && b2
-- Boolean or
#check b1 || b2
-- Boolean "true"
#check true

/- Evaluate -/
#eval 5 * 4
#eval m + 2
#eval b1
#eval b2
#eval b1 || b2
#eval b1 && b1
#eval b1 != b2
#eval b1 == b2
#eval !b2

--

def square (a : Nat) : Nat := a^2
#eval square 3

#check Nat × Nat
#check Prod Nat Nat

#check Nat -> Nat


#check Nat.succ
#check (0, 1)
#check Nat.add
#check Nat.succ 2
#check Nat.add 3
#check Nat.add 5 2
#check (5, 9).1
#check (5, 9).2
#eval Nat.succ 2
#eval Nat.add 5 2
#eval (5, 9).1
#eval (5, 9).2

--

#eval Nat.sub 6 2
#eval Nat.mul 15 2

-- Division on nats is floor division
#eval Nat.div 6 4

-- oh, tuples are strange
#check (1, 2, 3, 4, 5)
#eval (1, 2, 3, 4, 5).2.2.2.2

--

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α
#check F α
#check F Nat
#check G α
#check G α β
#check G α Nat

#check Type
#check Type 1
#check Type 32
-- #check Type 33 or above is bad
#check Type 0
#check List
#check Prod
#check Prod Type
#check Prod Type (Type 2)
#check Prod (Type 5) (Type 2)
#check Prod Type Type

--

#check fun (x : Nat) => x + 5
#eval (fun (x : Nat) => x + 5) 4
-- λ is deprecated in Mathlib4
#eval (fun (x : Nat) => x + 5) 41

-- The below examples are equivalent
#check fun (x : Nat) => fun (y : Bool) => if not y then x + 1 else x + 2
#eval (fun (x : Nat) => fun (y : Bool) => if not y then x + 1 else x + 2) 3 True
#eval (fun (x : Nat) => fun (y : Bool) => if not y then x + 1 else x + 2) 3 False

#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2

#check fun x y => if not y then x + 1 else x + 2
#eval (fun x y => if not y then x + 1 else x + 2) 3 True
#eval (fun x y => if not y then x + 1 else x + 2) 3 False

--

def triple (a : Nat) : Nat := 3 * a
def add_three (a : Nat) : Nat := a + 3

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#eval compose Nat Nat Nat triple square 5

--

def doTwice (α : Type) (h : α → α) (y : α) : α :=
  h (h y)

def doThrice {α : Type*} (h : α → α) (x : α) : α :=
  h (h (h x))

#eval add_three 0
#eval doTwice Nat add_three 0
#eval doThrice add_three 0
#eval compose Nat Nat Nat (doTwice Nat add_three) add_three 0
#eval compose Nat Nat Nat (doThrice add_three) add_three 0

-- Sections exist for scoping

section useful
variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose1 := g (f x)
def doTwice1 := h (h x)
def doThrice1 := h (h (h x))
end useful
