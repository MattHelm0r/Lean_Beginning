import Mathlib

/-
Working through example in this video:
https://www.youtube.com/watch?v=I2zaPoj3G50
-/

def seq_conv_to_L (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n > N, |a n - L| < ε

theorem squeeze_thm (a b c : ℕ → ℝ) (L : ℝ)
  (c_le_b : c ≤ b) (b_le_a : b ≤ a)
  (a_to_L : seq_conv_to_L a L)
  (c_to_L : seq_conv_to_L c L) :
  seq_conv_to_L b L := by
    unfold seq_conv_to_L
    intro eps
    intro eps_is_positive!

    -- Grab the Ns for which the sequence is forced
    -- to be epsilon-close to L
    obtain ⟨N₁, hN₁⟩ := a_to_L eps eps_is_positive!
    obtain ⟨N₂, hN₂⟩ := c_to_L eps eps_is_positive!

    let N : ℕ := max N₁ N₂

    have N₂_le_N : N₂ ≤ N := by
      exact Nat.le_max_right N₁ N₂

    have N₁_le_N : N₁ ≤ N := by
      exact Nat.le_max_left N₁ N₂

    use N
    intro n n_gt_N
    rw [abs_lt]
    refine ⟨sorry, sorry⟩
