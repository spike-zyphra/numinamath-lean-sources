import Mathlib

theorem algebra_152918 (x : ℝ) (hx : x > 0) :
    (1 / 2) * (3 * x ^ 2 - 1) = (x ^ 2 - 50 * x - 10) * (x ^ 2 + 25 * x + 5) ↔
    x = 25 + 2 * √159 := by
  constructor
  · -- Assume (1 / 2) * (3 * x ^ 2 - 1) = (x ^ 2 - 50 * x - 10) * (x ^ 2 + 25 * x + 5) prove x = 25 + 2 * √159
    intro h_eq
    have h1 : (x - (25 + 2 * Real.sqrt 159)) * (x - (25 - 2 * Real.sqrt 159)) = 0 := by
      nlinarith [sq_nonneg (x - (25 + 2 * Real.sqrt 159)), sq_nonneg (x - (25 - 2 * Real.sqrt 159)), Real.sqrt_nonneg 159, Real.sq_sqrt (show 0 ≤ (159 : ℝ) by norm_num), sq_pos_of_pos (show Real.sqrt 159 > 0 by positivity), mul_pos (show 0 < x by linarith) (show 0 < (x + 25) by nlinarith)]
    cases' (mul_eq_zero.mp h1) with h2 h3
    · -- Case where x - (25 + 2 * √159) = 0
      linarith
    · -- Case where x - (25 - 2 * √159) = 0
      have h4 : x = 25 - 2 * Real.sqrt 159 := by linarith
      nlinarith [Real.sqrt_pos.mpr (show 159 > 0 by norm_num : (159 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (159 : ℝ) by norm_num : (159 : ℝ) ≥ 0), Real.sqrt_nonneg 159, sq_nonneg (Real.sqrt 159 - 6)]
  · -- Assume x = 25 + 2 * √159 prove (1 / 2) * (3 * x ^ 2 - 1) = (x ^ 2 - 50 * x - 10) * (x ^ 2 + 25 * x + 5)
    intro h_eq
    rw [h_eq]
    nlinarith [Real.sqrt_pos.mpr (show 159 > 0 by norm_num : (159 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (159 : ℝ) by norm_num : (159 : ℝ) ≥ 0), sq_nonneg (Real.sqrt 159 - 6)]