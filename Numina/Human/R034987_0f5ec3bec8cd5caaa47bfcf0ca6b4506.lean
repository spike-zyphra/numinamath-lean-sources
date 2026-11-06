import Mathlib

  theorem algebra_132534 {a : ℝ} (ha : 2 * a - 1 / a = 3) :
  16 * a ^ 4 + 1 / a ^ 4 = 161 := by
    have h1 : a ≠ 0 := by
      by_contra h
      rw [h] at ha
      norm_num at ha
    have h2 : 4 * a ^ 2 + 1 / a ^ 2 = 13 := by
      have h2 : 2 * a - 1 / a = 3 := ha
      field_simp [h1] at *
      nlinarith [sq_nonneg (2 * a - 1 / a)]
    have h3 : 16 * a ^ 4 + 1 / a ^ 4 = 161 := by
      have h3 : 4 * a ^ 2 + 1 / a ^ 2 = 13 := h2
      field_simp [h1] at *
      nlinarith [sq_nonneg (4 * a ^ 2 + 1 / a ^ 2)]
    exact h3