import Mathlib.Data.Real.Basic

example (a b c : ℝ) : a * b * c = b * (a * c) := by
    rw [mul_comm a b]
    rw [mul_assoc b a c]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
    rw [mul_comm c b]
    rw [mul_assoc b c a]
    rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
    rw [← mul_assoc a b c]
    rw [mul_comm a b]
    rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
    rw [mul_comm]
    rw [mul_assoc]

theorem dog (a b c : ℝ) : a * (b * c) = b * (a * c) := by
    rw [← mul_assoc a]
    rw [mul_comm a]
    rw [mul_assoc]

example (a b c d e f : ℝ) (h_1 : a * b = c * d) (h_2 : e = f) : a * (b * e) = c * (d * f) := by
    rw [← mul_assoc, h_1, h_2, mul_assoc]

example (a b c d e f : ℝ) (h_1 : b * c = e * f) : a * b * c * d = a * e * f * d := by
    rw [mul_assoc a, h_1, ← mul_assoc a]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
    rw [← sub_self d]
    nth_rw 1 [hyp']
    rw [mul_comm a]
    exact hyp

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
    rw [hyp, mul_comm, hyp', sub_self]

example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
    rw [add_mul, mul_add, mul_add, ← add_assoc, mul_comm b a, two_mul (a * b), ← add_assoc]

example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
    calc
        (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
            rw [mul_add, add_mul, add_mul]
        _ = a * a + (b * a + a * b) + b * b := by
            rw [← add_assoc, add_assoc (a * a)]
        _ = a * a + 2 * (a * b) + b * b := by
            rw [mul_comm b a, ← two_mul]

example (a b c d : ℝ) : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
    rw [add_mul, mul_add, mul_add, ← add_assoc]

example (a b c d : ℝ) : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
    calc
        (a + b) * (c + d) = a * (c + d) + b * (c + d) := by
            rw [add_mul]
        _ = a * c + a * d + (b * c + b * d) := by
            rw [mul_add, mul_add]
        _ = a * c + a * d + b * c + b * d := by
            rw [← add_assoc]

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  calc
    (a + b) * (a - b)
        = a * a + b * a - a * b - b * b := by rw [mul_sub, add_mul, add_mul, ← sub_sub]
    _ = a * a + a * b - a * b - b * b := by rw [mul_comm b a]
    _ = a * a - b * b := by simp
    _ = a ^ 2 - b ^ 2 := by rw [← pow_two a, ← pow_two b]

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
