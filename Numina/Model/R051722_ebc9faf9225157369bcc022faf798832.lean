import Mathlib

theorem algebra_283870 :
    IsGreatest {z : ℝ | ∃ x y, z = x^2 + y^2 ∧ x^2 + y^2 = 2 * x - 2 * y + 2} (6 + 4 * √2) := by
  constructor
  · -- Show that 6 + 4 * sqrt(2) is attainable.
    use 1 + Real.sqrt 2, -1 - Real.sqrt 2
    constructor
    · -- Compute $z = x^2 + y^2$.
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    · -- Verify the constraint.
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  · -- Show that any z in the set is less than 6 + 4 * sqrt(2).
    intro z h
    rcases h with ⟨x, y, hz, heq⟩
    nlinarith [sq_nonneg (x - (1 + Real.sqrt 2)), sq_nonneg (y - (-1 - Real.sqrt 2)), 
          Real.sqrt_nonneg 2, 
          Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
          sq_nonneg ((x - 1) + (y + 1)), sq_nonneg ((x - 1) - (y + 1))]