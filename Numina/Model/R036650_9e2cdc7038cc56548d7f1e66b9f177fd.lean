import Mathlib

theorem algebra_10226 {r s : ℝ} (h : ∀ x, 11*x^2-44*x-99 = 0 ↔ (x+r)^2 = s) :
    r + s = 11 := by 
  have h1 := h (2 + Real.sqrt 13)
  have h_eq1 : 11 * (2 + Real.sqrt 13) ^ 2 - 44 * (2 + Real.sqrt 13) - 99 = 0 := by
    nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show 0 ≤ (13 : ℝ) by norm_num)]
  have h2 := h1.mp h_eq1
  have h1' := h (2 - Real.sqrt 13)
  have h_eq2 : 11 * (2 - Real.sqrt 13) ^ 2 - 44 * (2 - Real.sqrt 13) - 99 = 0 := by
    nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show 0 ≤ (13 : ℝ) by norm_num)]
  have h2' := h1'.mp h_eq2
  have h_eq3 : (2 + Real.sqrt 13 + r) ^ 2 = (2 - Real.sqrt 13 + r) ^ 2 := by
    linarith [h2, h2']
  have h_eq4 : (2 + r) * Real.sqrt 13 = 0 := by
    nlinarith [h_eq3, Real.sqrt_pos.mpr (show (0 : ℝ) < (13 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
  have h_eq5 : r = -2 := by
    cases' (mul_eq_zero.mp h_eq4) with h6 h7
    · -- Case r + 2 = 0
      linarith
    · -- Case Real.sqrt 13 = 0
      exfalso
      have h8 : Real.sqrt 13 > 0 := by
        positivity
      linarith
  have h_eq6 : s = 13 := by
    rw [h_eq5] at h2
    have h_eq7 : (2 + Real.sqrt 13 + (-2) ) ^ 2 = s := by
      linarith [h2]
    have h_eq8 : (2 + Real.sqrt 13 + (-2) ) ^ 2 = 13 := by
      nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    linarith [h_eq7, h_eq8]
  linarith [h_eq5, h_eq6]