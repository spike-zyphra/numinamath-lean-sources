import Mathlib


theorem algebra_118101 {a b : ℚ} (h : a^3 * b + a * b^3 + 2 * a^2 * b^2 + 2 * a + 2 * b + 1 = 0) :
    ∃ r : ℚ, Real.sqrt (1 - a * b) = r := by
  use abs ((a + b + 1) / (a + b) : ℚ)
  have h2 : a + b ≠ 0 := by
    by_contra h3
    have hb : b = -a := by
      have : a + b = 0 := by
        exact_mod_cast h3
      linarith
    rw [show b = -a by linarith [hb]] at h
    nlinarith [sq_nonneg (a^2), sq_nonneg (a), sq_nonneg (a + 1), sq_nonneg (a - 1)]
  have h3 : (1 - a * b : ℝ) = ((a + b + 1) / (a + b) : ℝ) ^ 2 := by
    have h3 : (1 - a * b : ℚ) = ((a + b + 1) / (a + b) : ℚ) ^ 2 := by
      have h4 : a + b ≠ 0 := h2
      field_simp [h4]
      nlinarith [sq_nonneg (a + b + 1), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b - 1), sq_nonneg (a * b)]
    exact_mod_cast h3

  have h4 : Real.sqrt (1 - a * b) = abs ((a + b + 1) / (a + b) : ℝ) := by
    rw [show (1 - a * b : ℝ) = ((a + b + 1) / (a + b) : ℝ) ^ 2 by linarith [h3]]
    rw [Real.sqrt_sq_eq_abs]

  have h5 : abs ((a + b + 1) / (a + b) : ℝ) = (abs ((a + b + 1) / (a + b) : ℚ) : ℝ) := by
    simp [Rat.cast_abs]

  rw [h4, h5]
  all_goals norm_num