import Mathlib

theorem algebra_3606 {a b : ℝ} (h₀ : 20 / (a + b) + 17 / (b - a) = 21) (h₁ : 212 / (b - a) - 1100 / (a + b) = -8) : 10 * a + b = 23 := by
  have h2 : a + b ≠ 0 := by
    by_contra h
    have h3 : a + b = 0 := by linarith
    rw [h3] at h₀ h₁
    field_simp [(show a + b = (0 : ℝ) by linarith), (show b - a ≠ 0 by
      by_contra h4
      have h5 : b = a := by linarith
      rw [h5] at h₀ h₁
      norm_num [h5] at h₀ h₁
      all_goals linarith
    )] at h₀ h₁
    all_goals linarith
  have h3 : b - a ≠ 0 := by
    by_contra h
    have h4 : b - a = 0 := by linarith
    have h5 : b = a := by linarith
    rw [h5] at h₀ h₁
    field_simp [(show a + a ≠ 0 by
      intro h6
      apply h2
      linarith
    ), (show b - a = (0 : ℝ) by linarith)] at h₀ h₁
    all_goals linarith
  have eq1 : 20 * (b - a) + 17 * (a + b) = 21 * (a + b) * (b - a) := by
    have h4 : a + b ≠ 0 := h2
    have h5 : b - a ≠ 0 := h3
    field_simp [h4, h5] at h₀
    linarith [h₀]
  have eq2 : 212 * (a + b) - 1100 * (b - a) = -8 * (a + b) * (b - a) := by
    have h4 : a + b ≠ 0 := h2
    have h5 : b - a ≠ 0 := h3
    field_simp [h4, h5] at h₁
    linarith [h₁]
  have eq3 : a + b = 5 := by
    nlinarith [sq_pos_of_ne_zero (show b - a ≠ 0 by assumption), sq_pos_of_ne_zero (show a + b ≠ 0 by assumption), sq_nonneg (a - 2), sq_nonneg (b - 3)]
  have eq4 : b - a = 1 := by
    nlinarith [sq_pos_of_ne_zero (show b - a ≠ 0 by assumption), sq_pos_of_ne_zero (show a + b ≠ 0 by assumption), sq_nonneg (a - 2), sq_nonneg (b - 3)]
  have h4 : b = a + 1 := by
    linarith
  have h5 : a = 2 := by
    linarith [eq3, h4]
  have h6 : b = 3 := by
    linarith [h4, h5]
  linarith [h5, h6]