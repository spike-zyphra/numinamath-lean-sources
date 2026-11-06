import Mathlib

open Real

theorem algebra_14143 : IsGreatest {x * y * z * (x + y + z) / ((x + y) ^ 2 * (y + z) ^ 2) | (x : ℝ) (y : ℝ) (z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)} (1 / 4) := by 
  constructor
  · -- Show 1/4 is in the set.
    use 1, Real.sqrt 2 - 1, 1
    have h01 : 0 < (1 : ℝ) := by linarith
    have h02 : 0 < Real.sqrt 2 - 1 := by
      have h101 : 1 < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
      linarith
    have h03 : 0 < (1 : ℝ) := by linarith
    have h04 : ((1 * (Real.sqrt 2 - 1) * 1 * (1 + (Real.sqrt 2 - 1) + 1)) / ((1 + (Real.sqrt 2 - 1)) ^ 2 * ((Real.sqrt 2 - 1) + 1) ^ 2)) = 1 / 4 := by
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have h3 : (1 + (Real.sqrt 2 - 1) + 1) = Real.sqrt 2 + 1 := by ring
      have h4 : (1 + (Real.sqrt 2 - 1)) = Real.sqrt 2 := by ring
      have h5 : ((Real.sqrt 2 - 1) + 1) = Real.sqrt 2 := by ring
      rw [h3, h4, h5]
      field_simp [show Real.sqrt 2 ≠ 0 by nlinarith, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    exact ⟨h01, h02, h03, h04⟩
  · -- Show that 1/4 is greatest in the set
    intro r hr
    rcases hr with ⟨x, y, z, hx, hy, hz, hr⟩
    have h6 : 0 < (x + y) ^ 2 * (y + z) ^ 2 := by positivity
    have h7 : x * y * z * (x + y + z) ≤ (1 / 4) * ((x + y) ^ 2 * (y + z) ^ 2) := by
      have h8 : 4 * (x * y * z * (x + y + z)) ≤ (x + y) ^ 2 * (y + z) ^ 2 := by
        nlinarith [sq_nonneg (x * (y + z) - z * (x + y)), sq_nonneg (y ^ 2 - x * z), sq_nonneg ((x + y) * (y + z) - 2 * (y * (x + y + z))), sq_nonneg (x - z), sq_nonneg (y - (Real.sqrt 2 - 1) * x), sq_nonneg (y - (Real.sqrt 2 - 1) * z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, sq_nonneg (x + y + z - 2 * y), sq_nonneg (x * (x + y) - z * (y + z)), sq_nonneg (x * y - y * z), sq_nonneg (y * (x - z)), sq_nonneg (y ^ 2 - x * z)]
      linarith
    have h7' : x * y * z * (x + y + z) / ((x + y) ^ 2 * (y + z) ^ 2) ≤ 1 / 4 := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      linarith
    linarith