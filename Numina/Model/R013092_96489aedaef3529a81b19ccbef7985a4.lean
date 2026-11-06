import Mathlib

open Real

theorem inequalities_597423 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1) :
    sqrt x / (4 * x + 1) + sqrt y / (4 * y + 1) + sqrt z / (4 * z + 1) ≤
    3 * sqrt 3 / 7 := by
  have h2 : sqrt x / (4 * x + 1) ≤ ( (sqrt 3 / 7) - ( (3 * sqrt 3 / 98) * (x - 1/3) )) := by
    have h3 : 0 < 4 * x + 1 := by nlinarith
    have h4 : sqrt x / (4 * x + 1) ≤ ( (sqrt 3 / 7) - ( (3 * sqrt 3 / 98) * (x - 1/3) )) := by
      apply (div_le_iff₀ (by nlinarith)).mpr
      have h7 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < (3 : ℝ))
      have h8 : 0 < (sqrt x : ℝ) := Real.sqrt_pos.mpr hx
      nlinarith [ Real.sqrt_nonneg (x), Real.sqrt_nonneg (3 : ℝ), sq (Real.sqrt x - Real.sqrt 3 / 3 ), sq (x - 1/3 ), sq_nonneg (x - 1/3 ), sq_nonneg (sqrt x - (sqrt 3 / 3)), Real.sq_sqrt (show 0 ≤ x by linarith), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith), mul_pos (show 0 < (sqrt 3 : ℝ) by nlinarith) (show 0 < (sqrt x : ℝ) by nlinarith), mul_pos (show 0 < x by linarith) (show 0 < z by linarith) ]
    linarith
  have h3 : sqrt y / (4 * y + 1) ≤ ( (sqrt 3 / 7) - ( (3 * sqrt 3 / 98) * (y - 1/3) )) := by
    have h3 : 0 < 4 * y + 1 := by nlinarith
    have h4 : sqrt y / (4 * y + 1) ≤ ( (sqrt 3 / 7) - ( (3 * sqrt 3 / 98) * (y - 1/3) )) := by
      apply (div_le_iff₀ (by nlinarith)).mpr
      have h7 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < (3 : ℝ))
      have h8 : 0 < (sqrt y : ℝ) := Real.sqrt_pos.mpr hy
      nlinarith [ Real.sqrt_nonneg (y), Real.sqrt_nonneg (3 : ℝ), sq (Real.sqrt y - Real.sqrt 3 / 3 ), sq (y - 1/3 ), sq_nonneg (y - 1/3 ), sq_nonneg (sqrt y - (sqrt 3 / 3)), Real.sq_sqrt (show 0 ≤ y by linarith), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith), mul_pos (show 0 < (sqrt 3 : ℝ) by nlinarith) (show 0 < (sqrt y : ℝ) by nlinarith), mul_pos (show 0 < y by linarith) (show 0 < x by linarith) ]
    linarith
  have h4 : sqrt z / (4 * z + 1) ≤ ( (sqrt 3 / 7) - ( (3 * sqrt 3 / 98) * (z - 1/3) )) := by
    have h3 : 0 < 4 * z + 1 := by nlinarith
    have h4 : sqrt z / (4 * z + 1) ≤ ( (sqrt 3 / 7) - ( (3 * sqrt 3 / 98) * (z - 1/3) )) := by
      apply (div_le_iff₀ (by nlinarith)).mpr
      have h7 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < (3 : ℝ))
      have h8 : 0 < (sqrt z : ℝ) := Real.sqrt_pos.mpr hz
      nlinarith [ Real.sqrt_nonneg (z), Real.sqrt_nonneg (3 : ℝ), sq (Real.sqrt z - Real.sqrt 3 / 3 ), sq (z - 1/3 ), sq_nonneg (z - 1/3 ), sq_nonneg (sqrt z - (sqrt 3 / 3)), Real.sq_sqrt (show 0 ≤ z by linarith), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith), mul_pos (show 0 < (sqrt 3 : ℝ) by nlinarith) (show 0 < (sqrt z : ℝ) by nlinarith), mul_pos (show 0 < z by linarith) (show 0 < x by linarith) ]
    linarith
  nlinarith [ Real.sqrt_nonneg (x : ℝ), Real.sqrt_nonneg (y : ℝ), Real.sqrt_nonneg (z : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ z by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith) ]