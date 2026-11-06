import Mathlib


open Real


lemma lemma_1 : (Real.sqrt 7 - 2) ^ 2 = 11 - 4 * Real.sqrt 7 := by
  have h1 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  nlinarith


theorem algebra_1296 {x y : ℝ} (hx : x = 11 + 4 * √7) (hy : y = 11 - 4 * √7) : x ^ ((3 : ℝ) / 2) + y ^ ((3 : ℝ) / 2) = 38 * √7 := by
  have h1 : (11 + 4 * Real.sqrt 7) = (Real.sqrt 7 + 2) ^ 2 := by
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)]

  have h2 : (11 - 4 * Real.sqrt 7) = (Real.sqrt 7 - 2) ^ 2 := by
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)]

  have hx2 : x = (Real.sqrt 7 + 2 : ℝ) ^ 2 := by
    rw [hx]
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)]

  have hy2 : y = (Real.sqrt 7 - 2 : ℝ) ^ 2 := by
    rw [hy]
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)]

  have hx3 : x ^ ((3 : ℝ) / 2) = (Real.sqrt 7 + 2) ^ 3 := by
    rw [hx2]
    have h4 : ( (Real.sqrt 7 + 2 : ℝ) ^ 2 ) ^ ((3 : ℝ) / 2) = ( (Real.sqrt 7 + 2 : ℝ) ) ^ (3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)]
    have h5 : ( (Real.sqrt 7 + 2 : ℝ) ) ^ (3 : ℝ) = ( (Real.sqrt 7 + 2 : ℝ) ) ^ 3 := by
      norm_cast
    rw [h4, h5]

  have hy3 : y ^ ((3 : ℝ) / 2) = (Real.sqrt 7 - 2 : ℝ) ^ 3 := by
    rw [hy2]
    have h4 : ( (Real.sqrt 7 - 2 : ℝ) ^ 2 ) ^ ((3 : ℝ) / 2) = ( (Real.sqrt 7 - 2 : ℝ) ) ^ (3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)]
    have h5 : ( (Real.sqrt 7 - 2 : ℝ) ) ^ (3 : ℝ) = ( (Real.sqrt 7 - 2 : ℝ) ) ^ 3 := by
      norm_cast
    rw [h4, h5]

  rw [hx3, hy3]

  nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (7 : ℝ) ≥ 0 by norm_num), sq_nonneg (Real.sqrt 7 ^ 2 - 7), sq_nonneg (Real.sqrt 7 - 2), sq_nonneg (Real.sqrt 7 + 2)]