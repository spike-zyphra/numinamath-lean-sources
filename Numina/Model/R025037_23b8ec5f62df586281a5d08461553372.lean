import Mathlib

theorem algebra_321612 (f : ℝ → ℝ) (hf : f = fun x => x^3 - Real.sqrt 3 * x^2 - (2 * Real.sqrt 3 + 1) * x + 3 + Real.sqrt 3) :
    f (Real.sqrt 3 + 1) = 0 ∧ f ((-1 + Real.sqrt (1 + 4 * Real.sqrt 3)) / 2) = 0 ∧ f ((-1 - Real.sqrt (1 + 4 * Real.sqrt 3)) / 2) = 0 := by
  have eq1 : f (Real.sqrt 3 + 1) = 0 := by
    rw [hf]
    have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
    simp [pow_two, pow_succ, h1, Real.mul_self_sqrt (show 0 ≤ (3 : ℝ) by norm_num) ]
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (Real.sqrt 3 ^ 3)]
  have eq2 : f ((-1 + Real.sqrt (1 + 4 * Real.sqrt 3)) / 2) = 0 := by
    rw [hf]
    have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
    have h2 : Real.sqrt (1 + 4 * Real.sqrt 3) ^ 2 = 1 + 4 * Real.sqrt 3 := by
      apply Real.sq_sqrt
      positivity -- show 1 + 4 * Real.sqrt 3 ≥ 0
    simp [pow_two, pow_succ, h1, h2, Real.mul_self_sqrt (show 0 ≤ (3 : ℝ) by norm_num) ]
    <;> nlinarith [Real.sqrt_nonneg (1 + 4 * Real.sqrt 3), Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt (1 + 4 * Real.sqrt 3) ^ 2), sq_nonneg ((Real.sqrt 3) ^ 2), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (1 + 4 * Real.sqrt 3) by positivity) ]
  have eq3 : f ((-1 - Real.sqrt (1 + 4 * Real.sqrt 3)) / 2) = 0 := by
    rw [hf]
    have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
    have h2 : Real.sqrt (1 + 4 * Real.sqrt 3) ^ 2 = 1 + 4 * Real.sqrt 3 := by
      apply Real.sq_sqrt
      positivity -- show 1 + 4 * Real.sqrt 3 ≥ 0
    simp [pow_two, pow_succ, h1, h2, Real.mul_self_sqrt (show 0 ≤ (3 : ℝ) by norm_num) ]
    <;> nlinarith [Real.sqrt_nonneg (1 + 4 * Real.sqrt 3), Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt (1 + 4 * Real.sqrt 3) ^ 2), sq_nonneg ((Real.sqrt 3) ^ 2), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (1 + 4 * Real.sqrt 3) by positivity) ]
  exact ⟨eq1, eq2, eq3⟩