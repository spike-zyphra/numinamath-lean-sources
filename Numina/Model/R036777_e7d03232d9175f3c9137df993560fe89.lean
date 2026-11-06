import Mathlib

open Real Set

theorem algebra_200787 :
  IsGreatest {z : ℝ | ∃ x y, z = |x + 2 * y| ∧ 2 * x ^ 2 + 3 * y ^ 2 ≤ 12} (Real.sqrt 22) := by
  constructor
  · -- Show that Real.sqrt 22 is in the set
    use (3 * Real.sqrt 22 / 11), (4 * Real.sqrt 22 / 11)
    constructor
    · -- Show z = |x + 2 * y|
      have h1 : Real.sqrt 22 ≥ 0 := by positivity
      have h2 : (3 * Real.sqrt 22 / 11 : ℝ) + 2 * (4 * Real.sqrt 22 / 11 : ℝ) = Real.sqrt 22 := by
        nlinarith
      have h_abs : |(3 * Real.sqrt 22 / 11 : ℝ) + 2 * (4 * Real.sqrt 22 / 11 : ℝ)| = Real.sqrt 22 := by
        rw [h2]
        all_goals
          norm_num [abs_of_nonneg, h1]
      linarith [h_abs]
    · -- Show 2 * x ^ 2 + 3 * y ^ 2 ≤ 12
      have h3 : Real.sqrt 22 ^ 2 = 22 := Real.sq_sqrt (show (0 : ℝ) ≤ 22 by norm_num)
      nlinarith [Real.sqrt_nonneg 22, h3]
  · -- Show that Real.sqrt 22 is greatest
    intro z h
    rcases h with ⟨x, y, h_eq, h_le⟩
    have h1 : (x + 2 * y) ^ 2 ≤ 22 := by
      nlinarith [sq_nonneg (x - 3 * y / 2), sq_nonneg (2 * x - (4 * y)), sq_nonneg (x * 3 - y * 4), sq_nonneg (y - (4 / 3) * x), sq_nonneg (x * 2 - y * 3 / 2), sq_nonneg (x * 3 - y * 4), sq_nonneg (x * Real.sqrt 22 - y * 4 / 11 * Real.sqrt 22), sq_nonneg (y * 3 / 11 - x * 4 / 11), Real.sqrt_pos.mpr (show (0 : ℝ) < (22 : ℝ) by norm_num : (0 : ℝ) < (22 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (22 : ℝ) by norm_num : (0 : ℝ) ≤ (22 : ℝ)), sq_nonneg (x + 2 * y), sq_nonneg (x - 2 * y)]
    have h2 : |x + 2 * y| ≤ Real.sqrt 22 := by
      have h_le' : (x + 2 * y) ^ 2 ≤ (22 : ℝ) := h1
      have h3 : Real.sqrt ((x + 2 * y) ^ 2) ≤ Real.sqrt (22 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h4 : |x + 2 * y| = Real.sqrt ((x + 2 * y) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
      linarith [h4, h3]
    linarith [h_eq, h2, Real.sqrt_nonneg 22]