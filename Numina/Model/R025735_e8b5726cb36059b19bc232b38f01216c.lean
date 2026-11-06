import Mathlib

theorem algebra_189836 {x : ℝ} (hx : x = 9 + 4 * Real.sqrt 5) :
    (x ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) = 3 := by
  have h1 : Real.sqrt 5 ^ 2 = 5 := by
    rw [Real.sq_sqrt]
    all_goals linarith
  have h2 : (9 + 4 * Real.sqrt 5) * (9 - 4 * Real.sqrt 5) = 1 := by
    nlinarith [h1, Real.sqrt_nonneg 5]
  have h3 : Real.sqrt 5 ≥ 0 := by
    apply Real.sqrt_nonneg
  have h4 : 0 ≤ (9 + 4 * Real.sqrt 5 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 5, h1]
  have h5 : 0 ≤ (9 - 4 * Real.sqrt 5 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 5, h1, Real.sqrt_nonneg 5]
  have ha1 : ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (9 + 4 * Real.sqrt 5 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul]
    norm_num
    all_goals nlinarith
  have hb1 : ((9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (9 - 4 * Real.sqrt 5 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul]
    norm_num
    all_goals nlinarith
  rw [hx]
  have h6 : ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + ((9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 18 := by
    nlinarith [ha1, hb1, h2]
  have hab : ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) * ((9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) = 1 := by
    have h7 : ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) * ((9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) =
        ((9 + 4 * Real.sqrt 5 : ℝ) * (9 - 4 * Real.sqrt 5 : ℝ)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.mul_rpow]
      all_goals nlinarith
    rw [h7, h2]
    norm_num
  have hS : ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 - 3 * ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) - 18 = 0 := by
    nlinarith [sq_nonneg ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3) - (9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)), Real.sqrt_nonneg 5, Real.sqrt_nonneg 5]
  have hS2 : ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3) - 3) * (((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 + 3 * ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) + 6) = 0 := by
    nlinarith [hS]
  cases' (mul_eq_zero.mp hS2) with hS3 hS4
  · -- First case where $S - 3 = 0$ therefore $S = 3$
    linarith
  · -- Show that the quadratic part has no real solutions
    nlinarith [sq_nonneg ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3) - (9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)), Real.sqrt_nonneg 5, sq_nonneg (Real.sqrt 5), h1]