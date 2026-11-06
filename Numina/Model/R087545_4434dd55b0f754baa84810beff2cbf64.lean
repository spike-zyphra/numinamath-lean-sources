import Mathlib

theorem algebra_297128 : (∃ x, (3 + Real.sqrt 13) / 2 = x ∧ (-3 + Real.sqrt 13) / 2 = 1 / x) := by
  use (3 + Real.sqrt 13) / 2
  constructor
  · -- Show (3 + Real.sqrt 13) / 2 = x
    rfl
  · -- Show (-3 + Real.sqrt 13) / 2 = 1 / x
    field_simp [(show (3 + Real.sqrt 13 : ℝ) ≠ 0 by
      by_contra h
      have h1 : Real.sqrt 13 = -3 := by linarith
      have h2 : Real.sqrt 13 ≥ 0 := Real.sqrt_nonneg 13
      linarith [Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num : (13 : ℝ) > 0), h1]
    )]
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]