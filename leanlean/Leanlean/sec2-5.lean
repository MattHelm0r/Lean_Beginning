import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Order.Defs.PartialOrder

variable {α : Type*} [PartialOrder α]
variable (x y z : α)
#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y := by
  apply lt_iff_le_and_ne

variable {β : Type*} [Lattice β]
variable (x y z : β)
#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
#check inf_comm
#check sup_comm


example (x y : β) : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · apply le_inf
    · exact inf_le_right        -- x ⊓ y ≤ y
    exact inf_le_left         -- x ⊓ y ≤ x
  · apply le_inf
    · exact inf_le_right        -- y ⊓ x ≤ x
    exact inf_le_left         -- y ⊓ x ≤ y

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  ·

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · apply le_sup
    · exact sup_le_right
    exact sup_

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply sup_assoc


/- All these are quicker ways of proving these:
example (x y : β) : x ⊓ y = y ⊓ x := by
  apply le_antisymm

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply inf_assoc

example : x ⊔ y = y ⊔ x := by
  apply sup_comm

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply sup_assoc
-/

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_inf
    apply inf_le_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  sorry
