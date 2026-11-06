import Mathlib

theorem algebra_252079 :
    ∀ p : ℝ, ∃ x : ℝ, 3 * (p + 2) * x^2 - p * x - (4 * p + 7) = 0 := by
  intro p
  have h1 : 49 * p ^ 2 + 180 * p + 168 ≥ 0 := by
    nlinarith [sq_nonneg (49 * p + 90), sq_nonneg (p + 90 / 49)]
  by_cases hp : p + 2 = 0
  · -- case p = -2
    have hp2 : p = -2 := by linarith
    use -1 / 2
    rw [hp2]
    norm_num
  · -- case p ≠ -2
    have hp2 : p + 2 ≠ 0 := by assumption
    use (p + Real.sqrt (49 * p^2 + 180 * p + 168)) / (6 * (p + 2))
    field_simp [hp2]
    nlinarith [Real.sqrt_nonneg (49 * p ^ 2 + 180 * p + 168), Real.sq_sqrt (show (0 : ℝ) ≤ 49 * p ^ 2 + 180 * p + 168 by nlinarith [h1])]