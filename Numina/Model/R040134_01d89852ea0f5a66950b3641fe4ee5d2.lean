import Mathlib

theorem algebra_18767 : IsGreatest {(k : ℝ) | ∃ x y : ℝ, y = k * x ∧ (x - 3)^2 + (y - 3)^2 = 6} (3 + 2 * √2) := by
  constructor
  · -- Show that 3 + 2 * sqrt 2 is in the set
    use (2 - Real.sqrt 2), (2 + Real.sqrt 2)
    constructor
    · -- Show that y = (3 + 2 * sqrt 2) * x
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Show that (x - 3) ^ 2 + (y - 3) ^ 2 = 6
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Show that 3 + 2 * sqrt 2 is an upper bound
    intro k hk
    rcases hk with ⟨x, y, h_eq, h_eq2⟩
    nlinarith [sq_nonneg (x - (2 - Real.sqrt 2)), sq_nonneg (y - (2 + Real.sqrt 2)), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (k - (3 + 2 * Real.sqrt 2)), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (x * Real.sqrt 2 - y + 2 * x), sq_nonneg (y * Real.sqrt 2 - x + 2 * y), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2)]