import Mathlib

open Real

theorem algebra_127311 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    a + sqrt b + (c ^ ((1 : ℝ) / 3)) ≤ 5 / 4 + 2 * sqrt 3 / 9 := by

  have h1 : sqrt b ≤ b + 1 / 4 := by
    have h2 : sqrt b ≤ b + 1 / 4 := by
      have h3 : sqrt b ≥ 0 := Real.sqrt_nonneg b
      have h4 : b ≥ 0 := by linarith
      have h5 : (sqrt b) ^ 2 = b := Real.sq_sqrt (by linarith)
      nlinarith [sq_nonneg (sqrt b - 1 / 2), sq_nonneg (b - 1 / 4), Real.sqrt_nonneg b, Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith)]
    linarith

  have h2 : (c : ℝ) ^ ((1 : ℝ) / 3) ≤ c + 2 * sqrt 3 / 9 := by
    have h3 : (c : ℝ) ^ ((1 : ℝ) / 3) ≤ c + 2 * sqrt 3 / 9 := by
      have h4 : (c : ℝ) ^ ((1 : ℝ) / 3) ≥ 0 := by positivity
      have h5 : c ≥ 0 := by linarith
      have h6 : ((c : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = c := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals nlinarith
      nlinarith [sq_nonneg ((c : ℝ) ^ ((1 : ℝ) / 3) - (sqrt 3 / 3)), sq_nonneg ((c : ℝ) - (1 / (3 * sqrt 3))), 
        Real.sqrt_nonneg (3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), 
        sq_nonneg ((c : ℝ) ^ ((1 : ℝ) / 3) - (sqrt 3 / 3)), 
        sq_nonneg ((c : ℝ) - (1 / (3 * sqrt 3))), 
        Real.sqrt_nonneg (3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), 
        mul_nonneg (Real.sqrt_nonneg (3)) (Real.sqrt_nonneg (3)), 
        sq_nonneg (sqrt 3 ^ 2 - 3)]
    linarith

  have h3 : a + sqrt b + (c ^ ((1 : ℝ) / 3)) ≤ a + (b + 1 / 4) + (c + 2 * sqrt 3 / 9) := by
    linarith [h1, h2]

  have h4 : a + (b + 1 / 4) + (c + 2 * sqrt 3 / 9) = (a + b + c) + 1 / 4 + 2 * sqrt 3 / 9 := by
    ring

  have h5 : (a + b + c) = 1 := by linarith

  linarith [h3, h4, h5, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]