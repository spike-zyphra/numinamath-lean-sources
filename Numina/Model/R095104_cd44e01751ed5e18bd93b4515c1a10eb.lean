import Mathlib

theorem algebra_7818 {x C : ℝ} (hx : x ≥ 0) (h : x + Real.sqrt x = C) :
    x = (1 + 2 * C - Real.sqrt (1 + 4 * C)) / 2 := by
  have h1 : Real.sqrt x = C - x := by linarith
  have h2 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
  have h3 : C - x ≥ 0 := by linarith [h1, h2]
  have h4 : (Real.sqrt x) ^ 2 = (C - x) ^ 2 := by
    rw [h1]
  have h5 : (Real.sqrt x) ^ 2 = x := by
    exact Real.sq_sqrt hx
  rw [h5] at h4
  -- Expanding to quadratic equation x^2 - (2 * C + 1) * x + c^2 = 0
  have h6 : x ^ 2 - (2 * C + 1) * x + C ^ 2 = 0 := by
    nlinarith
  have h7 : (x - (2 * C + 1 + Real.sqrt (1 + 4 * C)) / 2) * (x - (2 * C + 1 - Real.sqrt (1 + 4 * C)) / 2) = 0 := by 
    nlinarith [Real.sqrt_nonneg (1 + 4 * C), Real.sq_sqrt (show (1 + 4 * C) ≥ 0 by nlinarith)]
  cases' (mul_eq_zero.1 h7) with h8 h9
  · -- Case where x = (2 * C + 1 + sqrt(1 + 4 * C)) / 2 which does not satisfy the required constraints
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (1 + 4 * C), Real.sq_sqrt (show (1 + 4 * C) ≥ 0 by nlinarith), sq_nonneg (Real.sqrt x - C), sq_nonneg ((Real.sqrt (1 + 4 * C)) - (Real.sqrt x + C - x))]
  · -- Case where x = (2 * C + 1 - sqrt(1 + 4 * C)) / 2 which is the required solution
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (1 + 4 * C), Real.sq_sqrt (show (1 + 4 * C) ≥ 0 by nlinarith), sq_nonneg (Real.sqrt x - C), sq_nonneg ((Real.sqrt (1 + 4 * C)) - (Real.sqrt x + C - x))]