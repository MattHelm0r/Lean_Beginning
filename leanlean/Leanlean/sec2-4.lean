import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
-/

example (a b : ℝ) : min a b = min b a := by
  apply le_antisymm
  · apply le_min
    · apply min_le_right
    apply min_le_left
  · apply le_min
    · apply min_le_right
    apply min_le_left

#check le_antisymm

example (a b : ℝ) : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  · apply h
  apply h

example (a b : ℝ) : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example (a b : ℝ) : max a b = max b a := by
  have ge_max : ∀ x y z : ℝ, x ≥ y → x ≥ z → x ≥ max y z := by
    exact fun x y z a a_1 ↦ max_le a a_1
  have h : ∀ x y : ℝ, max x y ≤ max y x := by
    intro x y
    apply ge_max
    · apply le_max_right
    apply le_max_left
  apply le_antisymm
  · apply h
  apply h

#check max_eq_right

example (a b c : ℝ) : min (min a b) c = min a (min b c) := by
  apply min_assoc

theorem aux (a b c : ℝ) : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · have h1 : min a b ≤ a := min_le_left a b
    simpa [add_comm] using add_le_add_left h1 c
    --simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right h1 c
  · have h2 : min a b ≤ b := min_le_right a b
    simpa [add_comm] using add_le_add_right h2 c

example (a b : ℝ) : |a| - |b| ≤ |a - b| := by
  sorry

#check sub_add_cancel
