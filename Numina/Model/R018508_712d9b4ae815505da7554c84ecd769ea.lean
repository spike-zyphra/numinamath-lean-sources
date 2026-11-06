import Mathlib

theorem algebra_203925 {x : ℝ} (hx : x > 0) :
    x = 1 + 1 / (1 + 1 / (1 + 1 / (1 + 1 / x))) ↔
    x = (1 + Real.sqrt 5) / 2 := by
  constructor
  · -- Assume x = 1 + 1 / (1 + 1 / (1 + 1 / (1 + 1 / x)))
    intro h_eq
    have eq1 : x + 1 ≠ 0 := by linarith
    have eq2 : 2 * x + 1 ≠ 0 := by linarith
    have eq3 : 3 * x + 2 ≠ 0 := by linarith
    have eq4 : 5 * x + 3 ≠ 0 := by nlinarith
    field_simp [eq1, eq2, eq3, eq4, hx] at h_eq
    have h_eq2 : x ^ 2 - x - 1 = 0 := by
      nlinarith
    have h_eq3 : x ^ 2 - x - 1 = 0 := h_eq2
    have h_pos : x > 0 := hx
    have h_eq4 : x = (1 + Real.sqrt 5) / 2 := by
      have h1 : x ^ 2 - x - 1 = 0 := h_eq3
      have h2 : (x - (1 + Real.sqrt 5) / 2) * (x - (1 - Real.sqrt 5) / 2) = 0 := by
        nlinarith [h1, Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h2) with h3 h4
      · -- Case where x = (1 + sqrt 5)/2.
        linarith
      · -- Case where x = (1 - sqrt 5)/2.
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    linarith
  · -- Assume x = (1 + Real.sqrt 5) / 2
    intro h_eq
    have h_pos : x > 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h_eq]
    have h_eq2 : x ^ 2 - x - 1 = 0 := by
      nlinarith [h_eq, Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    have eq1 : x + 1 ≠ 0 := by linarith
    have eq2 : 2 * x + 1 ≠ 0 := by linarith
    have eq3 : 3 * x + 2 ≠ 0 := by linarith
    have eq4 : 5 * x + 3 ≠ 0 := by nlinarith
    field_simp [eq1, eq2, eq3, eq4, h_pos] at *
    nlinarith