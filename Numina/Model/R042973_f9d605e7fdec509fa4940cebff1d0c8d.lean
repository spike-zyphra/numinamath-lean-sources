import Mathlib
theorem algebra_609256 : IsGreatest {S : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ x ^ 2 - x * y + 2 * y ^ 2 = 8 ∧ S = x ^ 2 + x * y + 2 * y ^ 2}  ((72 + 32 * √2) / 7):= by
  constructor
  · -- Show that (72 + 32 * √2) / 7 is in the set
    use Real.sqrt ((4 * (4 + Real.sqrt 2)) / 7) * Real.sqrt 2, Real.sqrt ((4 * (4 + Real.sqrt 2)) / 7)
    constructor
    · -- Show x > 0
      positivity
    constructor
    · -- Show y > 0
      positivity
    constructor
    · -- Show x ^ 2 - x * y + 2 * y ^ 2 = 8
      have h1 : Real.sqrt ((4 * (4 + Real.sqrt 2)) / 7) ^ 2 = (4 * (4 + Real.sqrt 2)) / 7 := by
        rw [Real.sq_sqrt]
        positivity
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (4 * (4 + Real.sqrt 2) / 7 : ℝ) by positivity), Real.sqrt_nonneg (4 * (4 + Real.sqrt 2) / 7), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt ((4 * (4 + Real.sqrt 2)) / 7) * (Real.sqrt 2 - 1)), sq_nonneg (Real.sqrt 2 - 2), Real.sqrt_nonneg 2]
    · -- Show S = x ^ 2 + x * y + 2 * y ^ 2
      have h1 : Real.sqrt ((4 * (4 + Real.sqrt 2)) / 7) ^ 2 = (4 * (4 + Real.sqrt 2)) / 7 := by
        rw [Real.sq_sqrt]
        positivity
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (4 * (4 + Real.sqrt 2) / 7 : ℝ) by positivity), Real.sqrt_nonneg (4 * (4 + Real.sqrt 2) / 7), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt ((4 * (4 + Real.sqrt 2)) / 7) * (Real.sqrt 2 - 1)), sq_nonneg (Real.sqrt 2 - 2), Real.sqrt_nonneg 2]
  · -- Show that (72 + 32 * √2) / 7 is greatest
    intro S hS
    rcases hS with ⟨x, y, hx, hy, h1, hS⟩
    nlinarith [sq_nonneg (x ^ 2 - 2 * y ^ 2), sq_nonneg (y * (x - y * Real.sqrt 2)), sq_nonneg (x - y * Real.sqrt 2), sq_nonneg (y ^ 2 - (4 * (4 + Real.sqrt 2) / 7)), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg ((x) * (x - 2 * y)), sq_nonneg ((y) * (x - 2 * y)), mul_pos hx hy, Real.sq_sqrt (show (0 : ℝ) ≤ (4 : ℝ) by norm_num)]