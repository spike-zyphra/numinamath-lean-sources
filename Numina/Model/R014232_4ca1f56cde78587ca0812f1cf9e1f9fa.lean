import Mathlib

theorem algebra_246088 {r s : ℝ}
    (hr : r = Real.sqrt 2 + Real.sqrt 3) (hs : s = Real.sqrt 215 + Real.sqrt 300) :
    Real.sqrt 6 = (r^2 - 5) / 2 ∧ s^2 > 1015 := by

  have hr_eq : r = Real.sqrt 2 + Real.sqrt 3 := by
    exact_mod_cast hr

  have h1 : Real.sqrt 6 = (r^2 - 5) / 2 := by
    rw [hr_eq]
    have h2 : (Real.sqrt 2 + Real.sqrt 3) ^ 2 = (Real.sqrt 2) ^ 2 + (Real.sqrt 3) ^ 2 + 2 * (Real.sqrt 2 * Real.sqrt 3) := by
      ring
    have h3 : (Real.sqrt 2) ^ 2 = 2 := by
      rw [Real.sq_sqrt]
      norm_num
    have h4 : (Real.sqrt 3) ^ 2 = 3 := by
      rw [Real.sq_sqrt]
      norm_num
    have h5 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
      have h5 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt (2 * 3 : ℝ) := by
        rw [← Real.sqrt_mul (by norm_num)]
        all_goals norm_num
      rw [h5]
      all_goals norm_num
    rw [h2, h3, h4, h5]
    field_simp
    <;> nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
  have h2 : s^2 > 1015 := by
    rw [hs]
    have h3 : (Real.sqrt 215 + Real.sqrt 300) ^ 2 =
      (Real.sqrt 215) ^ 2 + (Real.sqrt 300) ^ 2 + 2 * (Real.sqrt 215 * Real.sqrt 300) := by
      ring
    have h4 : (Real.sqrt 215) ^ 2 = 215 := by
      rw [Real.sq_sqrt]
      norm_num
    have h5 : (Real.sqrt 300) ^ 2 = 300 := by
      rw [Real.sq_sqrt]
      norm_num
    have h6 : Real.sqrt 215 * Real.sqrt 300 = Real.sqrt 64500 := by
      have h6 : Real.sqrt 215 * Real.sqrt 300 = Real.sqrt (215 * 300 : ℝ) := by
        rw [← Real.sqrt_mul (by norm_num)]
        all_goals norm_num
      rw [h6]
      all_goals norm_num
    rw [h3, h4, h5, h6]
    have h7 : Real.sqrt 64500 > 250 := by
      have h8 : (250 : ℝ) ^ 2 < (64500 : ℝ) := by norm_num
      have h9 : (250 : ℝ) < Real.sqrt (64500 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 64500, Real.sq_sqrt (show (0 : ℝ) ≤ (64500 : ℝ) by norm_num), h8]
      linarith [h9]
    nlinarith [Real.sqrt_nonneg 64500, Real.sq_sqrt (show (0 : ℝ) ≤ (64500 : ℝ) by norm_num), h7]

  constructor
  · exact h1
  · exact h2