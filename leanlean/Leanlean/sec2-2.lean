import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-
#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
-/
universe u

variable {R : Type u} [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring


theorem neg_add_cancel_left0 (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

theorem add_neg_cancel_right0 (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_comm]
  rw [add_comm b, add_assoc, neg_add_cancel_left]

theorem add_neg_cancel_right1 (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_comm b, neg_add_cancel, add_zero]

theorem add_left_cancel0 {a b c : R} (h : a + b = a + c) : b = c := by
  have : a + b + -a = a + c + -a := by rw [h]
  rwa [add_assoc a b, add_comm b, ← add_assoc, add_comm a,
      add_assoc, neg_add_cancel_left0, add_comm, neg_add_cancel_left0] at this

theorem add_right_cancel0 {a b c : R} (h : a + b = c + b) : a = c := by
  have : a + b + -b = c + b + -b := by rw [h]
  rw [add_neg_cancel_right0, add_neg_cancel_right0] at this
  exact this

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← add_mul, add_zero, add_zero]
  rw [add_left_cancel h]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  have : a + b + -a = -a := by
    rw [h, zero_add]
  rw[add_comm, ← add_assoc, neg_add_cancel, zero_add] at this
  symm
  exact this

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [add_comm] at h
  have := neg_eq_of_add_eq_zero h
  symm
  exact this

theorem neg_zero0 : -0 = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg0 (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  rw[← neg_add_cancel]

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_comm, neg_add_cancel]

theorem one_add_one_eq_two0 : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul0 (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two0, add_mul, one_mul]



variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)



variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

theorem mul_inv_cancel0 (a : G) : a * a⁻¹ = 1 := by
  sorry

theorem mul_one0 (a : G) : a * 1 = a := by
  sorry

theorem mul_inv_rev0 (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry
