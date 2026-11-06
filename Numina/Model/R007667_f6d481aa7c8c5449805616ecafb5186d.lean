import Mathlib

open Real

theorem algebra_16275 :4 * (1 / 2 : ℝ) * (2 * sin (π / 6)) * (2 * cos (π / 6)) = 2 * √3 := by
  have hsin : sin (π / 6) = 1 / 2 := by
    exact sin_pi_div_six
  have hcos : cos (π / 6) = √3 / 2 := by
    have h1 : cos (π / 6) = √3 / 2 := by
      exact cos_pi_div_six
    exact h1
  rw [hsin, hcos]
  ring_nf
  <;> field_simp
  <;> ring_nf <;> simp [Real.sqrt_sq]
  all_goals linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (3 : ℝ) > 0), Real.sqrt_nonneg 3]