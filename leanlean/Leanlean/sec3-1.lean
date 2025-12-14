import Mathlib.Data.Real.Basic
import Mathlib

#check ∀ x : ℝ, 0 ≤ x → |x| = x
#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → (h₁ : ε ≤ 1) → (h₂: |x| < ε) → (h₃ : |y| < ε) → |x * y| < ε := by
  

section
variable (a b δ : ℝ)
variable (h0 : 0 < δ) (h1 : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h0 h1
#check my_lemma a b δ h0 h1 ha hb
end

/-
Comment
-/
