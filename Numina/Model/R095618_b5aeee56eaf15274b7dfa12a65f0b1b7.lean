import Mathlib

theorem algebra_278252 (a b : ℝ) (ha : a ≠ 0) (hb : b > 0) (h : a + b = 1) :
    1 / abs a + 2 * abs a / b ≥ 2 * Real.sqrt 2 - 1 := by
  have h1 : b = 1 - a := by linarith
  by_cases ha1 : a ≥ 0
  · -- a ≥ 0, so |a| = a
    rw [abs_of_nonneg ha1]
    have ha2 : a > 0 := by
      by_contra h'
      push_neg at h'
      have h_a_zero : a = 0 := by linarith
      contradiction
    have hb1 : b > 0 := hb
    have pos1 : a > 0 := by linarith
    have pos2 : b > 0 := hb
    have h3 : 1 / a + 2 * a / b ≥ 2 * Real.sqrt 2 - 1 := by
      have pos1 : a > 0 := by linarith
      have pos2 : b > 0 := hb
      have h3 : 1 / a + 2 * a / b - (2 * Real.sqrt 2 - 1) ≥ 0 := by
        have pos3 : a * b > 0 := by positivity
        have h4 : 1 / a + 2 * a / b - (2 * Real.sqrt 2 - 1) =
            (b + 2 * a^2 - (2 * Real.sqrt 2 - 1) * (a * b)) / (a * b) := by 
          field_simp [pos1, pos2]
          ring
        rw [h4]
        have h5 : b + 2 * a^2 - (2 * Real.sqrt 2 - 1) * (a * b) ≥ 0 := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
            sq_nonneg (a - (Real.sqrt 2 - 1)), sq_nonneg (b - (2 - Real.sqrt 2)), 
            h, Real.sqrt_nonneg 2, mul_pos pos1 pos2]
        apply div_nonneg h5 (by positivity)
      linarith
    linarith
  · -- a < 0, so |a| = -a
    rw [abs_of_neg (not_le.mp ha1)]
    have ha2 : a < 0 := by linarith
    have hb1 : b > 0 := hb
    have h3 : 1 / (-a) + 2 * (-a) / b ≥ 2 * Real.sqrt 2 - 1 := by
      have pos1 : -a > 0 := by linarith
      have pos2 : b > 0 := hb
      have h3 : 1 / (-a) + 2 * (-a) / b - (2 * Real.sqrt 2 - 1) ≥ 0 := by
        have pos3 : (-a) * b > 0 := by positivity
        have h4 : 1 / (-a) + 2 * (-a) / b - (2 * Real.sqrt 2 - 1) =
            (b + 2 * a^2 - (2 * Real.sqrt 2 - 1) * (-a) * b) / ((-a) * b) := by 
          field_simp [pos1, pos2]
          ring
        rw [h4]
        have h5 : b + 2 * a^2 - (2 * Real.sqrt 2 - 1) * (-a) * b ≥ 0 := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
            sq_nonneg (a + (Real.sqrt 2 + 1)), sq_nonneg (b - (Real.sqrt 2 + 2)), 
            h, Real.sqrt_nonneg 2, mul_pos pos1 pos2]
        apply div_nonneg h5 (by positivity)
      linarith
    linarith