import Mathlib

theorem algebra_1063 (a : ℝ) (ha : a = √3 - 1) :
    a^5 - a^4 + a^3 + a^2 - a + 1 = 63 * √3 - 108 := by
  have h3 : a + 1 = √3 := by
    rw [ha]
    ring
  have h4 : a^2 + 2 * a - 2 = 0 := by
    have h5 : (a + 1) ^ 2 - 3 = 0 := by
      rw [h3]
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ (3 : ℝ)), sq_nonneg (√3 - 1)]
    nlinarith
  have ha2 : a^2 = -2 * a + 2 := by
    nlinarith
  have ha3 : a^3 = 6 * a - 4 := by
    calc
      a^3 = a * a^2 := by ring
      _ = a * (-2 * a + 2) := by rw [ha2]
      _ = -2 * a^2 + 2 * a := by ring
      _ = -2 * (-2 * a + 2) + 2 * a := by rw [ha2]
      _ = 6 * a - 4 := by ring
  have ha4 : a^4 = -16 * a + 12 := by
    calc
      a^4 = (a^2) ^ 2 := by ring
      _ = (-2 * a + 2) ^ 2 := by rw [ha2]
      _ = 4 * a^2 - 8 * a + 4 := by ring
      _ = 4 * (-2 * a + 2) - 8 * a + 4 := by rw [ha2]
      _ = -16 * a + 12 := by ring
  have ha5 : a^5 = 44 * a - 32 := by
    calc
      a^5 = a * a^4 := by ring
      _ = a * (-16 * a + 12) := by rw [ha4]
      _ = -16 * a^2 + 12 * a := by ring
      _ = -16 * (-2 * a + 2) + 12 * a := by rw [ha2]
      _ = 44 * a - 32 := by ring
  rw [ha5, ha4, ha3, ha2]
  nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ (3 : ℝ)), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), sq_nonneg (√3 ^ 2 - 1), sq_nonneg (√3 - 1), sq_nonneg (√3), sq_nonneg (√3 - 1), sq_nonneg (√3 ^ 2 - 3), sq_nonneg (√3 ^ 3 - (3 * √3)), sq_nonneg (√3 ^ 4 - (9)), sq_nonneg (√3 ^ 5 - (9 * √3)), sq_pos_of_pos (Real.sqrt_pos.mpr (show 0 < 3 by norm_num : (0 : ℝ) < (3 : ℝ))), 
          sq_nonneg (√3 * √3 - 3)]