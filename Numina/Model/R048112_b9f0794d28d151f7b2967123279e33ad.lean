import Mathlib

theorem algebra_198341 : (2 + Real.sqrt 3) / (Real.sqrt 6 - Real.sqrt 3 + Real.sqrt 2 - 1) =
    (1 / 2) * (Real.sqrt 3 + 1) * (Real.sqrt 2 + 1) := by
  have h1 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> ring_nf <;> norm_num
    <;> nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]

  -- Simplify the denominator to (sqrt 3 + 1) * (sqrt 2 - 1)
  have h2 : Real.sqrt 6 - Real.sqrt 3 + Real.sqrt 2 - 1 = (Real.sqrt 3 + 1) * (Real.sqrt 2 - 1) := by
    rw [h1]
    ring_nf
    <;> nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]

  rw [h2]

  -- Note that sqrt 2 - 1 is not zero
  have h4 : Real.sqrt 2 - 1 ≠ 0 := by
    have h5 : 1 < Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    nlinarith

  -- Note that sqrt 3 + 1 is not zero
  have h5 : Real.sqrt 3 + 1 ≠ 0 := by
    have h6 : 0 < Real.sqrt 3 := by
      apply Real.sqrt_pos.mpr
      all_goals norm_num
    nlinarith [Real.sqrt_nonneg 3]

  -- Multiply both sides by the conjugates to rationalize
  field_simp [(show Real.sqrt 2 - 1 ≠ 0 by exact h4), (show Real.sqrt 3 + 1 ≠ 0 by exact h5), mul_ne_zero h5 h4, sub_ne_zero.mpr h4]

  -- Use algebraic manipulations
  <;> ring_nf <;> rw [show Real.sqrt 2 ^ 2 = (2 : ℝ) by apply Real.sq_sqrt; all_goals linarith]
  <;> rw [show Real.sqrt 3 ^ 2 = (3 : ℝ) by apply Real.sq_sqrt; all_goals linarith]
  <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, Real.mul_self_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.mul_self_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show 0 ≤ (6 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3)]