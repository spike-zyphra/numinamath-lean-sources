import Mathlib

open Real Set
open scoped Real

theorem calculus_16657 : cot (45 * π / 180) = 1 := by
  have h1 : 45 * π / 180 = Real.pi / 4 := by
    linarith [Real.pi_pos]

  rw [h1]
  rw [cot_eq_cos_div_sin]
  have h2 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have h3 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
  rw [h2, h3]
  field_simp
  <;> linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]