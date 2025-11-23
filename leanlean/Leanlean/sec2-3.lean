import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-
#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤  b → b ≤ c → a ≤ c)

variable (h : a ≤ b) (h' : b ≤ c)
#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)
-/

example (x y z : ℝ) (h0 : x ≤ y) (h1 : y ≤ z) : x ≤ z := by
 apply le_trans
 · apply h0
 · apply h1

example (x y z : ℝ) (h0 : x ≤ y) (h1 : y ≤ z) : x ≤ z := by
  apply le_trans h0
  apply h1

example (x y z : ℝ) (h0 : x ≤ y) (h1 : y ≤ z) : x ≤ z :=
  le_trans h0 h1

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
  le_refl x

example (a b c d e : ℝ) (h0 : a ≤ b) (h1 : b < c) (h2 : c ≤ d) (h3 : d < e) : a < e := by
  apply lt_of_le_of_lt h0
  apply lt_trans h1
  apply lt_of_le_of_lt h2
  apply h3

example (a b c d e : ℝ) (h0 : a ≤ b) (h1 : b < c) (h2 : c ≤ d) (h3 : d < e) : a < e := by
  linarith

example (a b d : ℝ) (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
 linarith

example (a b c : ℝ) (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + Real.exp b ≤ 3 * a + Real.exp c := by
  linarith [Real.exp_le_exp.mpr h']

/-
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_left
-/

example (a b : ℝ) (h : a ≤ b) : Real.exp a ≤ Real.exp b := by
  rw [Real.exp_le_exp]
  exact h

example (a b c d e : ℝ) (h0 : a ≤ b) (h1 : c < d) : a + Real.exp c + e < b + Real.exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h0
    apply Real.exp_lt_exp.mpr h1
  apply le_refl

example (a c d e : ℝ) (h0 : d ≤ e) : c + Real.exp (a + d) ≤ c + Real.exp (a + e) := by
  apply add_le_add
  · apply le_refl
  apply Real.exp_le_exp.mpr
  apply add_le_add_left
  exact h0

example : (0 : ℝ) < 1 := by norm_num

example (a b : ℝ) (h : a ≤ b) : Real.log (1 + Real.exp a) ≤ Real.log (1 + Real.exp b) := by
  have h0 : 0 < 1 + Real.exp a := by
    apply add_pos
    · norm_num
    apply Real.exp_pos
  apply Real.log_le_log h0
  apply add_le_add_left
  apply Real.exp_le_exp.mpr
  apply h

example (a : ℝ) : 0 ≤ a ^ 2 := by
  --apply?
  exact sq_nonneg a

example (a b c : ℝ) (h : a ≤ b) : c - Real.exp b ≤ c - Real.exp a := by
  linarith [Real.exp_le_exp.mpr h]

example (a b c : ℝ) (h : a ≤ b) : c - Real.exp b ≤ c - Real.exp a := by
  --apply? used
  apply tsub_le_tsub_left ?_ c
  apply Real.exp_le_exp.mpr
  apply h

example (a b : ℝ) : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2 :=
  calc
    a^2- 2*a*b + b^2 = (a- b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  calc
    2*a*b = 2*a*b + 0 := by ring
    _ ≤ 2*a*b + (a^2- 2*a*b + b^2) := add_le_add (le_refl _) h
    _ = a^2 + b^2 := by ring

example (a b : ℝ) : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2- 2*a*b + b^2 :=
  calc
    a^2- 2*a*b + b^2 = (a- b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

example (a b : ℝ): |a*b| ≤ (a^2 + b^2)/2 := by sorry

/-
will need to use

#check abs_le'.mpr

for above (come back after 3.4)
-/
