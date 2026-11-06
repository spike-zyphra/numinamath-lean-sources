import Mathlib

theorem inequalities_602575 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (h : a + b + c + d = 1) :
    Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) +
    Real.sqrt (4 * d + 1) < 6 := by
  have ha1 : Real.sqrt (4 * a + 1) < 2 * a + 1 := by
    have g1 : (2 * a + 1) ^ 2 > 4 * a + 1 := by 
      nlinarith [sq_pos_of_pos ha, h]
    have g2 : (Real.sqrt (4 * a + 1)) ^ 2 = 4 * a + 1 := by 
      rw [Real.sq_sqrt]
      linarith
    nlinarith [Real.sqrt_nonneg (4 * a + 1), pow_two_nonneg (a - 1 / 2)]
  have hb1 : Real.sqrt (4 * b + 1) < 2 * b + 1 := by
    have g1 : (2 * b + 1) ^ 2 > 4 * b + 1 := by 
      nlinarith [sq_pos_of_pos hb, h]
    have g2 : (Real.sqrt (4 * b + 1)) ^ 2 = 4 * b + 1 := by 
      rw [Real.sq_sqrt]
      linarith
    nlinarith [Real.sqrt_nonneg (4 * b + 1), pow_two_nonneg (b - 1 / 2)]
  have hc1 : Real.sqrt (4 * c + 1) < 2 * c + 1 := by
    have g1 : (2 * c + 1) ^ 2 > 4 * c + 1 := by 
      nlinarith [sq_pos_of_pos hc, h]
    have g2 : (Real.sqrt (4 * c + 1)) ^ 2 = 4 * c + 1 := by 
      rw [Real.sq_sqrt]
      linarith
    nlinarith [Real.sqrt_nonneg (4 * c + 1), pow_two_nonneg (c - 1 / 2)]
  have hd1 : Real.sqrt (4 * d + 1) < 2 * d + 1 := by
    have g1 : (2 * d + 1) ^ 2 > 4 * d + 1 := by 
      nlinarith [sq_pos_of_pos hd, h]
    have g2 : (Real.sqrt (4 * d + 1)) ^ 2 = 4 * d + 1 := by 
      rw [Real.sq_sqrt]
      linarith
    nlinarith [Real.sqrt_nonneg (4 * d + 1), pow_two_nonneg (d - 1 / 2)]
  have hsum : Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) + Real.sqrt (4 * d + 1) < (2 * a + 1) + (2 * b + 1) + (2 * c + 1) + (2 * d + 1) := by
    linarith [ha1, hb1, hc1, hd1]
  have eqn : (2 * a + 1) + (2 * b + 1) + (2 * c + 1) + (2 * d + 1) = 6 := by
    nlinarith [h]
  nlinarith [hsum, eqn]