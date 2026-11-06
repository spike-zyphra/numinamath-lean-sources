import Mathlib

theorem algebra_315852 {x : ℝ} (hx : x ≠ 0) (h : x * Real.sqrt (x^2 + 3 * x + 18) - x * Real.sqrt (x^2 - 6 * x + 18) = 1) :
    2 * x * Real.sqrt (x^2 - 6 * x + 18) - 9 * x^3 = -1 := by
  have h1 : x * Real.sqrt (x^2 + 3 * x + 18) = 1 + x * Real.sqrt (x^2 - 6 * x + 18) := by
    linarith
  have h2 : (x * Real.sqrt (x^2 + 3 * x + 18)) ^ 2 = (1 + x * Real.sqrt (x^2 - 6 * x + 18)) ^ 2 := by
    rw [h1]
  have h3 : (x * Real.sqrt (x^2 + 3 * x + 18)) ^ 2 = x^2 * (x^2 + 3 * x + 18) := by
    have h3a : Real.sqrt (x^2 + 3 * x + 18) ^ 2 = x^2 + 3 * x + 18 := by
      exact Real.sq_sqrt (show (0 : ℝ) ≤ x^2 + 3 * x + 18 by
        nlinarith [sq_nonneg (x + 3 / 2)]
      )
    calc
      (x * Real.sqrt (x^2 + 3 * x + 18)) ^ 2 = x^2 * (Real.sqrt (x^2 + 3 * x + 18) ^ 2) := by
        ring
      _ = x^2 * (x^2 + 3 * x + 18) := by
        rw [h3a]
  have h4 : (1 + x * Real.sqrt (x^2 - 6 * x + 18)) ^ 2 = 1 + 2 * x * Real.sqrt (x^2 - 6 * x + 18) + x^2 * (x^2 - 6 * x + 18) := by
    have h4a : Real.sqrt (x^2 - 6 * x + 18) ^ 2 = x^2 - 6 * x + 18 := by
      exact Real.sq_sqrt (show (0 : ℝ) ≤ x^2 - 6 * x + 18 by
        nlinarith [sq_nonneg (x - 3)]
      )
    nlinarith [sq_nonneg (x * Real.sqrt (x^2 - 6 * x + 18)), h4a]
  rw [h3, h4] at h2
  have h5 : x^2 * (x^2 + 3 * x + 18) = 1 + 2 * x * Real.sqrt (x^2 - 6 * x + 18) + x^2 * (x^2 - 6 * x + 18) := by
    linarith
  have h6 : 9 * x^3 = 1 + 2 * x * Real.sqrt (x^2 - 6 * x + 18) := by
    nlinarith [h5]
  have h7 : 2 * x * Real.sqrt (x^2 - 6 * x + 18) = 9 * x^3 - 1 := by
    linarith
  nlinarith [h7]