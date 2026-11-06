import Mathlib

theorem algebra_237889 :
    IsLeast {n : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y * z * (x + y + z) = 1 ∧ n = (x + y) * (x + z)} 2 := by

  constructor
  · -- Let's prove 2 is in the set.
    use Real.sqrt 2 - 1, 1, 1
    constructor
    · -- Show x > 0
      have h1 : Real.sqrt 2 > 1 := by
        nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    constructor
    · -- Show y > 0
      norm_num
    constructor
    · -- Show z > 0
      norm_num
    constructor
    · -- Show x * y * z * (x + y + z) = 1
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    · -- Show n = (x + y) * (x + z)
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Now, let's prove the minimal.
    intro n hn
    rcases hn with ⟨x, y, z, hx, hy, hz, h₀, hn⟩
    nlinarith [sq_nonneg (x * (x + y + z) - 1), sq_nonneg (y * z - 1), sq_nonneg (x + y + z - 1 / x), sq_nonneg (x * y - x * z), sq_nonneg (y - z), sq_nonneg (x * (x + y + z) - y * z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, mul_pos (show 0 < x * y by nlinarith) (show 0 < x * z by nlinarith), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), sq_nonneg (x * (x + y + z) - 1), sq_nonneg (y * z - 1), mul_pos (show 0 < x * y by nlinarith) (show 0 < x * z by nlinarith)]