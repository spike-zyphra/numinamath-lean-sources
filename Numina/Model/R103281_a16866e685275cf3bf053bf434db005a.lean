import Mathlib

theorem algebra_112309 {x : ℝ} (hx : x = √2 + √3) :
    x ^ 4 - 10 * x ^ 2 + 1 = 0 := by
  rw [hx]
  have h1 : (√2 + √3) ^ 2 = 5 + 2 * √6 := by
    calc
      (√2 + √3) ^ 2 = (√2) ^ 2 + (√3) ^ 2 + 2 * (√2 * √3) := by ring
      _ = 2 + 3 + 2 * (√2 * √3) := by simp [Real.sq_sqrt]
      _ = 5 + 2 * (√2 * √3) := by ring
      _ = 5 + 2 * (√(2 * 3)) := by rw [Real.sqrt_mul (by norm_num)]
      _ = 5 + 2 * √6 := by norm_num
  have h2 : (√2 + √3) ^ 4 = 49 + 20 * √6 := by
    calc
      (√2 + √3) ^ 4 = ((√2 + √3) ^ 2) ^ 2 := by ring
      _ = (5 + 2 * √6) ^ 2 := by rw [h1]
      _ = 49 + 20 * √6 := by
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
  nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num),
          Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 6,
          Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num),
          h1, h2]