import Mathlib

open Real Set
open scoped Real

theorem calculus_23401 : arccos (-1 / sqrt 2) = 3 * π / 4 := by
  have h1 : cos (3 * π / 4) = -sqrt 2 / 2 := by
    have h4 : 3 * π / 4 = π - (π / 4) := by ring
    rw [h4]
    rw [cos_pi_sub]
    have h5 : cos (π / 4) = sqrt 2 / 2 := by
      exact cos_pi_div_four
    rw [h5]
    <;> ring
  have h2 : cos (3 * π / 4) = -1 / sqrt 2 := by
    rw [h1]
    have h6 : sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
    field_simp [h6, Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    <;> nlinarith [Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h7 : arccos (-1 / sqrt 2) = 3 * π / 4 := by
    rw [show -1 / sqrt 2 = cos (3 * π / 4) by linarith [h2]]
    have h3 : 0 ≤ 3 * π / 4 := by
      nlinarith [Real.pi_pos]
    have h4 : 3 * π / 4 ≤ π := by
      nlinarith [Real.pi_pos]
    rw [arccos_cos h3 h4]
  exact h7