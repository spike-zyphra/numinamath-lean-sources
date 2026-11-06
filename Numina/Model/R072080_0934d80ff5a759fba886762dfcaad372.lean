import Mathlib

open Real

theorem algebra_1685 (x : ℝ) (hx : 1 ≤ x ∧ x ≤ 2) : sqrt (x + 2 * sqrt (x - 1)) - sqrt (x - 2 * sqrt (x - 1)) = 2 * sqrt (x - 1) := by
  have hx1 : 1 ≤ x := hx.1
  have hx2 : x ≤ 2 := hx.2
  have h1 : 0 ≤ x - 1 := by linarith
  have h2 : sqrt (x - 1) ≥ 0 := Real.sqrt_nonneg (x - 1)
  have h3 : x + 2 * sqrt (x - 1) = (sqrt (x - 1) + 1) ^ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith [h1]), Real.sqrt_nonneg (x - 1)]
  have h4 : sqrt (x + 2 * sqrt (x - 1)) = sqrt (x - 1) + 1 := by
    rw [h3]
    have h5 : sqrt ((sqrt (x - 1) + 1) ^ 2) = sqrt (x - 1) + 1 := by
      rw [Real.sqrt_sq (show (sqrt (x - 1) + 1) ≥ 0 by
        linarith [Real.sqrt_nonneg (x - 1)]
      )]
    exact h5
  have h6 : x - 2 * sqrt (x - 1) = (sqrt (x - 1) - 1) ^ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith [h1]), Real.sqrt_nonneg (x - 1)]
  have h7 : sqrt (x - 2 * sqrt (x - 1)) = 1 - sqrt (x - 1) := by
    rw [h6]
    have h8 : sqrt (x - 1) ≤ 1 := by
      have h9 : x - 1 ≤ (1 : ℝ) := by linarith [h1, hx2]
      have h10 : sqrt (x - 1) ≤ sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h11 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      nlinarith [h11, Real.sqrt_nonneg (x - 1)]
    have h7a : (sqrt (x - 1) - 1) ≤ 0 := by
      nlinarith [Real.sqrt_nonneg (x - 1), h8]
    have h7b : sqrt ((sqrt (x - 1) - 1) ^ 2) = 1 - sqrt (x - 1) := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonpos h7a]
      all_goals linarith [Real.sqrt_nonneg (x - 1)]
    exact h7b
  rw [h4, h7]
  linarith [Real.sqrt_nonneg (x - 1)]