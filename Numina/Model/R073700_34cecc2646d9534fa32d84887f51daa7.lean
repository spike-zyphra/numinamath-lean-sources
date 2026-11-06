import Mathlib

theorem algebra_3983 (a : ℝ) : 4 * a^2 + 2 * a^2 * Real.sqrt 3 = 1 ↔
  a = (Real.sqrt 3 - 1) / 2 ∨ a = -(Real.sqrt 3 - 1) / 2:= by
  constructor
  · -- Forward Proof: If `4 * a^2 + 2 * a^2 * Real.sqrt 3 = 1`, then `a = (Real.sqrt 3 - 1) / 2 ∨ a = -(Real.sqrt 3 - 1) / 2`
    intro h
    have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) from by norm_num)
    have h2 : 0 < 2 + Real.sqrt 3 := by
      have sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num)
      nlinarith
    have h3 : Real.sqrt 3 - 1 > 0 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h8 : (a - (Real.sqrt 3 - 1) / 2) * (a + (Real.sqrt 3 - 1) / 2) = 0 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), h]
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- Case: `a - (Real.sqrt 3 - 1) / 2 = 0`
      left
      linarith
    · -- Case: `a + (Real.sqrt 3 - 1) / 2 = 0`
      right
      linarith
  · -- Reverse Proof: If `a = (Real.sqrt 3 - 1) / 2 ∨ a = -(Real.sqrt 3 - 1) / 2`, then `4 * a^2 + 2 * a^2 * Real.sqrt 3 = 1`
    rintro (ha | ha)
    · -- Case: `a = (Real.sqrt 3 - 1) / 2`
      rw [ha]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
    · -- Case: `a = -(Real.sqrt 3 - 1) / 2`
      rw [ha]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]