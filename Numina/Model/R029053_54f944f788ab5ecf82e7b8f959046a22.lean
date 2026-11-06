import Mathlib

theorem algebra_317876 {x : ℝ} (a : ℕ → ℝ) (h : ∀ x, (Real.sqrt 3 * x + Real.sqrt 2)^5 = ∑ i in Finset.range 6, a i * x^i) :
    (a 5 + a 3 + a 1)^2 - (a 4 + a 2 + a 0)^2 = 1 := by

  have eq1 := h 1
  have eq2 := h (0 : ℝ)
  have eq3 := h (-1 : ℝ)

  simp [Finset.sum_range_succ] at eq1 eq2 eq3

  have eq5 : (a 5 + a 3 + a 1) = ((Real.sqrt 3 * (1 : ℝ) + Real.sqrt 2)^5 - (Real.sqrt 3 * (-1 : ℝ) + Real.sqrt 2)^5) / 2 := by
    nlinarith

  have eq6 : (a 4 + a 2 + a 0) = ((Real.sqrt 3 * (1 : ℝ) + Real.sqrt 2)^5 + (Real.sqrt 3 * (-1 : ℝ) + Real.sqrt 2)^5) / 2 := by
    nlinarith

  rw [eq5, eq6]

  have h1 : (Real.sqrt 3 * (1 : ℝ) + Real.sqrt 2) * (Real.sqrt 3 * (-1 : ℝ) + Real.sqrt 2) = -1 := by 
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 ^ 2), sq_nonneg (Real.sqrt 2 ^ 2)]

  have h2 : (Real.sqrt 3 * (1 : ℝ) + Real.sqrt 2)^5 * (Real.sqrt 3 * (-1 : ℝ) + Real.sqrt 2)^5 = -1 := by 
    calc 
      (Real.sqrt 3 * (1 : ℝ) + Real.sqrt 2)^5 * (Real.sqrt 3 * (-1 : ℝ) + Real.sqrt 2)^5
          = ((Real.sqrt 3 * (1 : ℝ) + Real.sqrt 2) * (Real.sqrt 3 * (-1 : ℝ) + Real.sqrt 2)) ^ 5 := by ring
      _ = (-1 ) ^ 5 := by rw [h1]
      _ = -1 := by norm_num

  nlinarith [h1, h2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 ^ 2), sq_nonneg (Real.sqrt 2 ^ 2)]