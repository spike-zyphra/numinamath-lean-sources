import Mathlib

theorem algebra_198328 (x : ℝ) :
    x^2 + 5 * x + 4 = 5 * Real.sqrt (x^2 + 5 * x + 28) ↔ x = 4 ∨ x = -9 := by
  constructor
  · -- Assume the equation holds, prove the solutions
    intro h_eq
    have h1 : 0 ≤ Real.sqrt (x^2 + 5 * x + 28) := by positivity
    have h2 : x^2 + 5 * x + 4 ≥ 0 := by
      by_contra h
      push_neg at h
      have h3 : 5 * Real.sqrt (x^2 + 5 * x + 28) ≥ 0 := by
        nlinarith [show Real.sqrt (x ^ 2 + 5 * x + 28) ≥ 0 by positivity]
      nlinarith [Real.sqrt_nonneg (x^2 + 5 * x + 28), h3, Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 5 * x + 28 by nlinarith [sq_nonneg (x + 5 / 2)])]
    have h_eq2 : (x^2 + 5 * x + 4)^2 = 25 * (x^2 + 5 * x + 28) := by
      have h3 : Real.sqrt (x^2 + 5 * x + 28) ≥ 0 := by positivity
      have h4 : (5 * Real.sqrt (x^2 + 5 * x + 28)) ^ 2 = 25 * (x^2 + 5 * x + 28) := by
        calc
          (5 * Real.sqrt (x^2 + 5 * x + 28)) ^ 2 = 25 * (Real.sqrt (x^2 + 5 * x + 28) ) ^ 2 := by ring
          _ = 25 * (x^2 + 5 * x + 28) := by
            rw [Real.sq_sqrt]
            nlinarith [sq_nonneg (x + 5 / 2)]
      have h5 : (x^2 + 5 * x + 4) ^ 2 = (5 * Real.sqrt (x^2 + 5 * x + 28)) ^ 2 := by
        have h6 : x^2 + 5 * x + 4 = 5 * Real.sqrt (x^2 + 5 * x + 28) := h_eq
        rw [h6]
      nlinarith [h5, h4]
    have h_eq3 : (x - 4) * (x + 9) = 0 := by
      nlinarith [sq_nonneg (x^2 + 5 * x + 28 - 64), sq_nonneg (x + 9), sq_nonneg (x - 4), Real.sqrt_nonneg (x^2 + 5 * x + 28)]
    cases' (mul_eq_zero.1 h_eq3) with h_eq4 h_eq5
    · -- Case x - 4 = 0, so x = 4
      left
      linarith
    · -- Case x + 9 = 0, so x = -9
      right
      linarith
  · -- Assume the solutions, prove the equation
    rintro (h_eq | h_eq)
    · -- Case x = 4
      rw [h_eq]
      have h1 : Real.sqrt ((4 : ℝ) ^ 2 + 5 * (4 : ℝ) + 28) = (8 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1]
      norm_num
    · -- Case x = -9
      rw [h_eq]
      have h1 : Real.sqrt ((-9 : ℝ) ^ 2 + 5 * (-9 : ℝ) + 28) = (8 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1]
      norm_num