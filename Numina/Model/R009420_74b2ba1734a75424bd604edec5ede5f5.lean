import Mathlib

theorem algebra_9375 : IsLeast {a : ℝ | ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ 2 * x + 6 * y - x * y = 0 ∧ x + y = a} (8 + 4 * √3) := by
  constructor
  · -- Show that 8 + 4 * √3 is achievable with positive x and y where the constraint holds.
    use 6 + 2 * √3, 2 + 2 * √3
    constructor
    · -- Show x is positive
      positivity
    constructor
    · -- Show y is positive
      positivity
    constructor
    · -- Verify the constraint 2x + 6y - x * y = 0
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    · -- Verify x + y = 8 + 4 * √3
      ring_nf
  · -- Show that 8 + 4 * √3 is the least such value.
    intro a ha
    rcases ha with ⟨x, y, hx, hy, h1, h2⟩
    nlinarith [sq_nonneg (x - 6 - 2 * √3), sq_nonneg (y - 2 - 2 * √3), mul_pos (show (0 : ℝ) < √3 by apply Real.sqrt_pos.mpr; all_goals linarith) hx, mul_pos (show (0 : ℝ) < √3 by apply Real.sqrt_pos.mpr; all_goals linarith) hy, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (√3), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sqrt_nonneg 3, h1]