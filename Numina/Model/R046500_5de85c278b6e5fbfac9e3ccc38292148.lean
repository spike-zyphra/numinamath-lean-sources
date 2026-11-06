import Mathlib

theorem number_theory_4298 : ∃ (a : ℚ) (b : ℝ), 0 < a ∧ Irrational b ∧ ¬Irrational (a ^ b) := by
  use (1 : ℚ)
  use Real.sqrt 2
  constructor
  · -- Show that 0 < (1 : ℚ)
    norm_num
  constructor
  · -- Show that √2 is irrational
    native_decide
  · -- Show that (1 : ℚ) ^ (√2 : ℝ) is not irrational (i.e., is rational)
    have h1 : ((1 : ℚ) : ℝ) ^ (Real.sqrt 2 : ℝ) = (1 : ℝ) := by
      norm_num
    rw [h1]
    simp