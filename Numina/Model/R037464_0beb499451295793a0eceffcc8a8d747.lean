import Mathlib

theorem algebra_321038 {a : ℝ} (ha : abs a > 1) :
    (a + Real.sqrt (a ^ 2 - 1)) ^ 4 + 2 * (1 - 2 * a ^ 2) * (a + Real.sqrt (a ^ 2 - 1)) ^ 2 + 3 = 2 := by
  have h1 : a ^ 2 > 1 := by
    cases' abs_cases a with ha1 ha1
    · -- Case where a ≥ 0: abs a = a
      nlinarith
    · -- Case where a < 0: abs a = -a
      nlinarith
  have h2 : a ^ 2 - 1 > 0 := by
    linarith [h1]
  have h3 : Real.sqrt (a ^ 2 - 1) ^ 2 = a ^ 2 - 1 := by 
    exact Real.sq_sqrt (by linarith)
  have h4 : Real.sqrt (a ^ 2 - 1) ≥ 0 := by
    apply Real.sqrt_nonneg
  have h5 : (a + Real.sqrt (a ^ 2 - 1)) ^ 2 = 2 * a ^ 2 - 1 + 2 * a * Real.sqrt (a ^ 2 - 1) := by
    nlinarith [Real.sqrt_nonneg (a^2 -1), Real.sq_sqrt (show 0 ≤ (a^2 -1 : ℝ) by nlinarith)]
  have h6 : (a + Real.sqrt (a ^ 2 - 1)) ^ 4 = ((a + Real.sqrt (a ^ 2 - 1)) ^ 2) ^ 2 := by 
    ring
  rw [h6, h5]
  nlinarith [Real.sqrt_nonneg (a^2 - 1), Real.sq_sqrt (show 0 ≤ (a^2 -1 : ℝ) by nlinarith), sq_nonneg (a ^ 2 - 1), sq_nonneg (a + Real.sqrt (a ^ 2 - 1) - a), sq_nonneg (a - (Real.sqrt (a ^ 2 -1))), sq_nonneg (a + Real.sqrt (a ^ 2 -1) - (Real.sqrt (a ^ 2 -1)) -a)]