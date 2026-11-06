import Mathlib

open Real
open scoped BigOperators

theorem calculus_23217 :
  arccos ((4 * 1 + 4 * 4 + 7 * 1) / (Real.sqrt (4^2 + 4^2 + 7^2) * Real.sqrt (1^2 + 4^2 + 1^2))) * 180 / π = 45 := by 
  have h1 : (4 * 1 + 4 * 4 + 7 * 1 : ℝ) = 27 := by norm_num
  have h2 : Real.sqrt ((4 : ℝ) ^ 2 + (4 : ℝ) ^ 2 + (7 : ℝ) ^ 2) = (9 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h3 : Real.sqrt ((1 : ℝ) ^ 2 + (4 : ℝ) ^ 2 + (1 : ℝ) ^ 2) = 3 * Real.sqrt 2 := by
    have h4 : Real.sqrt ((1 : ℝ) ^ 2 + (4 : ℝ) ^ 2 + (1 : ℝ) ^ 2) = Real.sqrt 18 := by
      norm_num [Real.sqrt_eq_iff_sq_eq]
    rw [h4]
    have h5 : Real.sqrt 18 = (3 * Real.sqrt 2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num [Real.sq_sqrt]
    rw [h5]
    <;> ring_nf
    <;> norm_num [Real.sq_sqrt]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
  have h7 : (4 * 1 + 4 * 4 + 7 * 1 : ℝ) / (Real.sqrt ((4 : ℝ) ^ 2 + (4 : ℝ) ^ 2 + (7 : ℝ) ^ 2) * Real.sqrt ((1 : ℝ) ^ 2 + (4 : ℝ) ^ 2 + (1 : ℝ) ^ 2)) = Real.sqrt 2 / 2 := by
    rw [h1, h2, h3]
    have h6 : Real.sqrt 2 > 0 := by
      positivity
    field_simp
    <;> ring_nf
    <;> norm_num [Real.sq_sqrt]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
  rw [h7]
  have h5 : arccos (Real.sqrt 2 / 2) = Real.pi / 4 := by
    have h6 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      exact cos_pi_div_four
    rw [← h6]
    apply arccos_cos
    all_goals linarith [Real.pi_gt_314]
  rw [h5]
  field_simp
  <;> ring_nf
  <;> linarith [Real.pi_gt_314]