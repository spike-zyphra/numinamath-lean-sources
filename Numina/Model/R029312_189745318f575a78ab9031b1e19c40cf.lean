import Mathlib
open Real

/- Real numbers $x, y$ satisfy $2x^2 + 3y^2 = 6y$, then the maximum value of $x + y$ is ___          ___. -/
theorem algebra_8789 : IsGreatest {z : ℝ | ∃ x y, z = x + y ∧ 2 * x ^ 2 + 3 * y ^ 2 = 6 * y} ((2 + √10) / 2) := by
  constructor
  · -- Show that (2 + √10)/2 is in the set
    use 3 * Real.sqrt 10 / 10, (5 + Real.sqrt 10)/5
    constructor
    · -- Show z = x + y
      field_simp
      <;> nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)]
    · -- Show 2 * x ^ 2 + 3 * y ^ 2 = 6 * y
      ring_nf
      nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)]
  · -- Show that (2 + √10)/2 is the greatest element in the set
    intro z hz
    rcases hz with ⟨x, y, h_eq, h_eq1⟩
    nlinarith [sq_nonneg (x - 3 * Real.sqrt 10 / 10), sq_nonneg (y - (5 + Real.sqrt 10)/5), Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num), sq_nonneg (2 * x - 3 * (Real.sqrt 10)/5), sq_nonneg (y - (5 + Real.sqrt 10)/5), mul_nonneg (Real.sqrt_nonneg 10) (Real.sqrt_nonneg 10)]