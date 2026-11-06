import Mathlib

theorem number_theory_111721 (n : ℕ) (hn : n > 0) :
    ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ (a ^ 2 + a + 1 : ℝ) / (b ^ 2 + b + 1) = n ^ 2 + n + 1 := by
  use (n + 1) ^ 2
  use n + 1
  constructor
  · -- Show that a > 0
    have h1 : (n + 1) > 0 := by linarith
    have h2 : (n + 1) ^ 2 > 0 := by
      apply Nat.pow_pos
      exact h1
    linarith
  constructor
  · -- Show that b > 0
    have h1 : (n + 1) > 0 := by linarith
    linarith
  · -- Verify the equation
    field_simp
    <;> ring_nf <;> norm_num