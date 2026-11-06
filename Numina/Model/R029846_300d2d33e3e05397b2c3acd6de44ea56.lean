import Mathlib

open Real

theorem inequalities_5783 (a b : ℝ) (h₀ : 0 < b) (h₁ : b < a) :
    a + 1 / (b * (a - b)) ≥ 3 := by
  have h2 : 0 < a - b := by linarith
  have h3 : 0 < b * (a - b) := mul_pos h₀ h2
  have h4 : a + 1 / (b * (a - b)) - 3 ≥ 0 := by
    have h5 : a + 1 / (b * (a - b)) - 3 =
        (a * b * (a - b) + 1 - 3 * b * (a - b)) / (b * (a - b)) := by
      field_simp
      <;> ring
    rw [h5]
    have h6 : a * b * (a - b) + 1 - 3 * b * (a - b) ≥ 0 := by
      nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (b - 1), sq_nonneg (a - 2), sq_nonneg (b), sq_nonneg ((a - b) - 1), mul_pos h₀ (show 0 < a - b by linarith), mul_pos (show 0 < a - b by linarith) h₀, sq_nonneg (b - (a - b))]
    have h7 : (a * b * (a - b) + 1 - 3 * b * (a - b)) / (b * (a - b)) ≥ 0 := by
      apply div_nonneg
      linarith
      all_goals positivity
    linarith
  linarith