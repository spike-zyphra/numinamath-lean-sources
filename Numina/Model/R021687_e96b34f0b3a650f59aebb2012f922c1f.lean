import Mathlib

theorem algebra_165907 (x : ℝ) (hx : x + 3 ≥ 0) (h : (x + 7) ^ ((1 : ℝ) / 3) - Real.sqrt (x + 3) = 0) :
    x = 1 := by
  have h1 : (x + 7 : ℝ) ^ ((1 : ℝ) / 3) = Real.sqrt (x + 3) := by
    linarith
  have h3 : ((x + 7 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (x + 7 : ℝ) := by
    have h4 : ((x + 7 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (x + 7 : ℝ) ^ (1 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    rw [h4]
    norm_num
  have h2 : ((x + 7 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (Real.sqrt (x + 3)) ^ 3 := by
    rw [h1]
  have h6 : (x + 7 : ℝ) = (Real.sqrt (x + 3)) ^ 3 := by
    linarith [h2, h3]
  have h8 : (Real.sqrt (x + 3)) ^ 2 = (x + 3) := by
    rw [Real.sq_sqrt]
    linarith
  have h11 : (x + 7) ^ 2 = (x + 3) ^ 3 := by
    calc
      (x + 7) ^ 2 = (Real.sqrt (x + 3) * (x + 3)) ^ 2 := by
        have h10 : (x + 7 : ℝ) = (Real.sqrt (x + 3)) * (x + 3) := by
          have h11 : (Real.sqrt (x + 3)) ^ 3 = (Real.sqrt (x + 3)) * (x + 3) := by
            calc
              (Real.sqrt (x + 3)) ^ 3 
                  = (Real.sqrt (x + 3)) * (Real.sqrt (x + 3)) ^ 2 := by ring
              _   = (Real.sqrt (x + 3)) * (x + 3) := by rw [h8]
          linarith [h6, h11]
        rw [h10]
      _ = (Real.sqrt (x + 3)) ^ 2 * (x + 3) ^ 2 := by
        ring_nf
      _ = (x + 3) * (x + 3) ^ 2 := by
        rw [show (Real.sqrt (x + 3)) ^ 2 = (x + 3) by linarith [h8]]
        all_goals linarith
      _ = (x + 3) ^ 3 := by
        ring_nf
  have h12 : x ^ 3 + 8 * x ^ 2 + 13 * x - 22 = 0 := by
    nlinarith [sq_nonneg (x + 3), sq_nonneg (x - 1)]
  have h13 : (x - 1) * (x ^ 2 + 9 * x + 22) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h13) with h14 h15
  · -- x - 1 = 0, so x = 1
    linarith
  · -- x^2 + 9x + 22 = 0
    nlinarith [sq_nonneg (x + 9 / 2)]