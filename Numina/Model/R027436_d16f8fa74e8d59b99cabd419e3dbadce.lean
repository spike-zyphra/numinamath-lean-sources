import Mathlib

open Real Set
open scoped Real

theorem algebra_264086 {a b : ℝ} (ha : a = cos (3 / 2)) (hb : b = sin (1 / 10)) :
    a < b := by
  rw [ha, hb]
  have h1 : sin (1 / 10 : ℝ) = cos (Real.pi / 2 - (1 / 10 : ℝ)) := by
    rw [←cos_pi_div_two_sub]
    <;> ring_nf
  rw [h1]
  have h2 : (3 / 2 : ℝ) > (Real.pi / 2 - (1 / 10 : ℝ)) := by
    linarith [Real.pi_gt_31415, Real.pi_lt_31416]
  have h3 : cos (3 / 2 : ℝ) < cos (Real.pi / 2 - (1 / 10 : ℝ)) := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    all_goals
      linarith [Real.pi_gt_31415, Real.pi_lt_31416, Real.pi_pos]
  linarith