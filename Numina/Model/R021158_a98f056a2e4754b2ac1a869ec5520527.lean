import Mathlib

theorem algebra_207377 (x y : ℝ) (h : (2015 + x^2) * (2015 + y^2) = 2^22) :
    x + y ≤ 2 * Real.sqrt 33 ∧ ∃ x y, (2015 + x^2) * (2015 + y^2) = 2^22 ∧ x + y = 2 * Real.sqrt 33 := by
  have h1 : x + y ≤ 2 * Real.sqrt 33 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 33), sq_nonneg (x + y - 2 * Real.sqrt 33), 
      sq_nonneg (x - Real.sqrt 33), sq_nonneg (y - Real.sqrt 33),
      Real.sqrt_nonneg 33, Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 33) (Real.sqrt_nonneg 33),
      sq_nonneg (x * y + 33)]
  have h2 : ∃ x y, (2015 + x^2) * (2015 + y^2) = 2^22 ∧ x + y = 2 * Real.sqrt 33 := by
    use Real.sqrt 33, Real.sqrt 33
    constructor
    · -- Verify the equation
      have h_eq : (2015 + (Real.sqrt 33 : ℝ) ^ 2) * (2015 + (Real.sqrt 33 : ℝ) ^ 2) = (2 ^ 11) * (2 ^ 11) := by
        have h33 : (Real.sqrt 33 : ℝ) ^ 2 = (33 : ℝ) := Real.sq_sqrt (by norm_num)
        nlinarith [h33]
      norm_num at h_eq ⊢
      all_goals nlinarith [h_eq]
    · -- Verify x + y = 2 * Real.sqrt 33
      ring_nf
  constructor
  · exact h1
  · exact h2