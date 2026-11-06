import Mathlib

open Real Set
open scoped Real

theorem inequalities_249431 : tan (11 * π / 180) < 0.2 := by
  have h1 : 0 < 11 * π / 180 := by 
    nlinarith [Real.pi_pos, Real.pi_gt_31415, Real.pi_lt_31416]
  have h2 : 0 < Real.cos (11 * π / 180) := by 
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · -- Show that -π/2 < 11 * π / 180
      nlinarith [Real.pi_pos, Real.pi_gt_31415, Real.pi_lt_31416]
    · -- Show that 11 * π / 180 < π/2 
      nlinarith [Real.pi_pos, Real.pi_gt_31415, Real.pi_lt_31416]
  have h3 : Real.tan (11 * π / 180) = Real.sin (11 * π / 180) / Real.cos (11 * π / 180) := by
    rw [Real.tan_eq_sin_div_cos]
  rw [h3]
  have h4 : Real.sin (11 * π / 180) < 0.2 * Real.cos (11 * π / 180) := by
    have h11 : 0 < Real.sin (11 * π / 180) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · -- Show 0 < 11 * π / 180
        nlinarith [Real.pi_pos, Real.pi_gt_31415, Real.pi_lt_31416]
      · -- Show 11 * π / 180 < Real.pi
        nlinarith [Real.pi_pos, Real.pi_gt_31415, Real.pi_lt_31416]
    have h12 : 0 < Real.cos (11 * π / 180) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · -- Show -π/2 < 11 * π / 180
        nlinarith [Real.pi_pos, Real.pi_gt_31415, Real.pi_lt_31416]
      · -- Show 11 * π / 180 < π/2
        nlinarith [Real.pi_pos, Real.pi_gt_31415, Real.pi_lt_31416]
    have h13 : Real.sin (11 * π / 180) < (11 * π / 180) := by
      apply Real.sin_lt
      all_goals
        nlinarith [Real.pi_pos, Real.pi_gt_31415, Real.pi_lt_31416]
    nlinarith [Real.sin_sq_add_cos_sq (11 * π / 180), Real.sin_sq_add_cos_sq (11 * π / 180), mul_pos h11 h12, Real.pi_pos, Real.pi_gt_31415, Real.pi_lt_31416]
  have hc : 0 < Real.cos (11 * π / 180) := h2
  apply (div_lt_iff₀ hc).mpr
  all_goals 
    nlinarith [h4]