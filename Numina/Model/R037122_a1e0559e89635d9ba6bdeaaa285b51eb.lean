import Mathlib

theorem algebra_310432 {f : ℝ → ℝ}
    (hf : ∀ x, f x = x ^ 6 - 2 * Real.sqrt 2006 * x ^ 5 - x ^ 4 + x ^ 3 - 2 * Real.sqrt 2007 * x ^ 2 + 2 * x - Real.sqrt 2006) :
    f (Real.sqrt 2006 + Real.sqrt 2007) = Real.sqrt 2007 := by
  have h1 : f (Real.sqrt 2006 + Real.sqrt 2007) = (Real.sqrt 2006 + Real.sqrt 2007) ^ 6 - 2 * Real.sqrt 2006 * (Real.sqrt 2006 + Real.sqrt 2007) ^ 5 - (Real.sqrt 2006 + Real.sqrt 2007) ^ 4 + (Real.sqrt 2006 + Real.sqrt 2007) ^ 3 - 2 * Real.sqrt 2007 * (Real.sqrt 2006 + Real.sqrt 2007) ^ 2 + 2 * (Real.sqrt 2006 + Real.sqrt 2007) - Real.sqrt 2006 := by
    apply hf
  rw [h1]
  have h2 : Real.sqrt 2006 ≥ 0 := by positivity
  have h3 : Real.sqrt 2007 ≥ 0 := by positivity
  have h4 : Real.sqrt 2006 ^ 2 = 2006 := Real.sq_sqrt (by norm_num)
  have h5 : Real.sqrt 2007 ^ 2 = 2007 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2006, Real.sqrt_nonneg 2007, sq_nonneg (Real.sqrt 2006 - Real.sqrt 2007), sq_nonneg (Real.sqrt 2006 ^ 2 - 2006), sq_nonneg (Real.sqrt 2007 ^ 2 - 2007), Real.sq_sqrt (show (0 : ℝ) ≤ (2006 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2007 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 2006) (Real.sqrt_nonneg 2007), mul_nonneg (Real.sqrt_nonneg 2006) (Real.sqrt_nonneg 2007)]