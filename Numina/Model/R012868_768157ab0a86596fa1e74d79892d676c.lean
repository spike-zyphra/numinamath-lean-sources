import Mathlib

theorem algebra_13447 : ⌊(2 + √3)^4⌋ = 193 := by
  have h1 : (2 + Real.sqrt 3 : ℝ) ^ 4 = 97 + 56 * Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (2 + Real.sqrt 3), sq_nonneg (2 - Real.sqrt 3), sq_nonneg ((Real.sqrt 3) - 2), Real.sqrt_nonneg 3]
  rw [h1]
  have h2 : 193 ≤ (97 + 56 * Real.sqrt 3 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3 - 1.732), Real.sqrt_nonneg 3]
  have h3 : (97 + 56 * Real.sqrt 3 : ℝ) < 194 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3 - 1.732), Real.sqrt_nonneg 3]
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> try linarith [h2, h3]