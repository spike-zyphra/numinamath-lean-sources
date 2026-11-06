import Mathlib
theorem algebra_610847 (x : ℝ) : (2 * x + 1) * (3 * x + 1) * (5 * x + 1) * (30 * x + 1) = 10 ↔ x = (-4 + √31) / 15 ∨ x = (-4 - √31) / 15:= by
  constructor
  · -- Forward: if the equation holds, then it has solutions
    intro h
    have h1 : (2 * x + 1) * (3 * x + 1) * (5 * x + 1) * (30 * x + 1) - 10 = 0 := by linarith
    have h2 : (x - (-4 + Real.sqrt 31) / 15) * (x - (-4 - Real.sqrt 31) / 15) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (31: ℝ) > 0), Real.sq_sqrt (by norm_num : (0: ℝ) ≤ (31: ℝ)), sq_nonneg (x + 4 / 15), sq_nonneg (x + 4 / 15), sq_nonneg ((2 * x + 1) * (3 * x + 1) - (5 * x + 1) * (30 * x + 1)), sq_nonneg ((3 * x + 1) * (5 * x + 1) - (2 * x + 1) * (30 * x + 1)), Real.sqrt_nonneg 31, mul_nonneg (Real.sqrt_nonneg 31) (Real.sqrt_nonneg 31)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- First root
      left
      linarith
    · -- Second root
      right
      linarith
  · -- Backward: if x is a root, then it satisfies the equation
    rintro (h | h)
    · -- First solution
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show 0 < 31 by norm_num : (31: ℝ) > 0), Real.sq_sqrt (show 0 ≤ (31: ℝ) by norm_num : (0: ℝ) ≤ (31: ℝ)), Real.sqrt_nonneg 31, sq_nonneg ((-4 + Real.sqrt 31) / 15 + 4 / 15)]
    · -- Second solution
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show 0 < 31 by norm_num : (31: ℝ) > 0), Real.sq_sqrt (show 0 ≤ (31: ℝ) by norm_num : (0: ℝ) ≤ (31: ℝ)), Real.sqrt_nonneg 31, sq_nonneg ((-4 - Real.sqrt 31) / 15 + 4 / 15)]