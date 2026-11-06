import Mathlib

theorem inequalities_307748 (a : ℝ) (ha : a > 0) :
    (3 * a ^ 2) ^ ((1 : ℝ) / 3) ≤ 1 + (2 / 3) * a := by

  have h2 : (3 * a ^ 2 : ℝ) ^ ((1 : ℝ) / 3) ≤ (1 + (2 / 3) * a) := by
    have h3 : (3 * a ^ 2) ≤ (1 + (2 / 3) * a) ^ 3 := by
      nlinarith [sq_nonneg (a - 3), sq_nonneg (a ^ 2 - 3 * a), sq_nonneg (a - 1.5), sq_nonneg ((8 * a + 3) * (a - 3)), mul_pos ha (show 0 < (8 : ℝ) * a + 3 by nlinarith [ha] ) ]
    
    have h4 : (3 * a ^ 2 : ℝ) ^ ((1 : ℝ) / 3) ≤ ((1 + (2 / 3) * a) ^ 3 ) ^ ((1 : ℝ) / 3) := by
      apply Real.rpow_le_rpow
      · nlinarith
      · nlinarith [h3]
      all_goals nlinarith
  
    have h5 : ((1 + (2 / 3) * a) ^ 3 ) ^ ((1 : ℝ) / 3) = 1 + (2 / 3) * a := by
      have h5a : ((1 + (2 / 3) * a) ^ 3) ^ ((1 : ℝ) / 3) = 1 + (2 / 3) * a := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals nlinarith
  
      linarith
  
    linarith [h4, h5]

  linarith [h2]