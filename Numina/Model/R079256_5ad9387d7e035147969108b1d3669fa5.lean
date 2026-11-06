import Mathlib

theorem algebra_315158 (x : ℝ) (hx : -1/2 ≤ x ∧ x ≤ 1) :
    Real.sqrt (x^2 - 2*x + 1) + Real.sqrt (x^2 - 6*x + 9) +
    Real.sqrt (4*x^2 + 4*x + 1) = 5 := by

  have h1 : Real.sqrt (x^2 - 2 * x + 1) = |x - 1| := by
    have h2 : x^2 - 2 * x + 1 = (x - 1) ^ 2 := by ring
    rw [h2]
    rw [Real.sqrt_sq_eq_abs]

  have h3 : Real.sqrt (x^2 - 6 * x + 9) = |x - 3| := by
    have h4 : x^2 - 6 * x + 9 = (x - 3) ^ 2 := by ring
    rw [h4]
    rw [Real.sqrt_sq_eq_abs]

  have h5 : Real.sqrt (4*x^2 + 4*x + 1) = |2*x + 1| := by
    have h6 : 4*x^2 + 4*x + 1 = (2*x + 1) ^ 2 := by ring
    rw [h6]
    rw [Real.sqrt_sq_eq_abs]

  have h7 : |x - 1| = 1 - x := by
    have hx1 : x ≤ 1 := hx.right
    rw [abs_of_nonpos]
    linarith
    all_goals linarith

  have h8 : |x - 3| = 3 - x := by
    have hx2 : x ≤ 1 := hx.right
    have h9 : x - 3 ≤ 0 := by linarith
    rw [abs_of_nonpos h9]
    all_goals linarith
    all_goals linarith

  have h9 : |2*x + 1| = 2*x + 1 := by
    have hx3 : -1/2 ≤ x := hx.left
    have h10 : 2*x + 1 ≥ 0 := by linarith
    rw [abs_of_nonneg h10]
    all_goals linarith

  rw [h1, h3, h5]
  rw [h7, h8, h9]
  linarith