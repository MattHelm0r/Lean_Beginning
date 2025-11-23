import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

theorem prime_factor {n : ℕ} (h : 2 ≤ n) : ∃ (p : ℕ), Nat.Prime p ∧ (p ∣ n) := by sorry


theorem infinite_primes (n : ℕ) : ∃ (p : ℕ), Nat.Prime p ∧ p > n := by
  have : 2 ≤ Nat.factorial n + 1 := by
    rw [Nat.add_one_le_add_one_iff]
    apply Nat.add_one_le_of_lt
    exact Nat.factorial_pos n
  have := prime_factor this
  apply Exists.elim this
  intro p ph
  use p
  apply And.intro
  · exact ph.left
  by_contra np
  push_neg at np
  have : p ∣ Nat.factorial n := by
    apply Nat.dvd_factorial
    exact Nat.Prime.pos ph.left
    exact np
  have : p ∣ Nat.factorial n + 1- Nat.factorial n := by
    apply Nat.dvd_sub
    exact ph.right
    exact this
  have : p ∣ 1 := by
    rw [Nat.add_sub_cancel_left] at this
    exact this
  rw [Nat.dvd_one] at this
  have := Nat.Prime.ne_one ph.left
  contradiction
