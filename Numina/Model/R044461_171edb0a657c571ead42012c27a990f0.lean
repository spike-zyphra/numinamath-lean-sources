import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_258040 {z : ℂ}
  (hz : z = sqrt (Real.pi / (Real.exp 1 + Real.pi)) * (1 + Complex.I) +
    sqrt (Real.exp 1 / (Real.pi + Real.exp 1)) * (1 - Complex.I)) :
  abs z = Real.sqrt 2 := by
  rw [hz]
  have h : abs (sqrt (Real.pi / (Real.exp 1 + Real.pi)) * (1 + Complex.I) + sqrt (Real.exp 1 / (Real.pi + Real.exp 1)) * (1 - Complex.I)) =
      Real.sqrt ((sqrt (Real.pi / (Real.exp 1 + Real.pi)) * 1 + sqrt (Real.exp 1 / (Real.pi + Real.exp 1)) * 1)^2 + (sqrt (Real.pi / (Real.exp 1 + Real.pi)) * 1 + sqrt (Real.exp 1 / (Real.pi + Real.exp 1)) * (-1))^2) := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
    <;> norm_num
    <;> ring
    <;> norm_num
    all_goals norm_num
  rw [h]
  have h_eq : (sqrt (Real.pi / (Real.exp 1 + Real.pi)) * 1 + sqrt (Real.exp 1 / (Real.pi + Real.exp 1)) * 1) ^ 2 + (sqrt (Real.pi / (Real.exp 1 + Real.pi)) * 1 + sqrt (Real.exp 1 / (Real.pi + Real.exp 1)) * (-1))^2 = 2 := by
    have h1 : sqrt (Real.pi / (Real.exp 1 + Real.pi)) ^ 2 = Real.pi / (Real.exp 1 + Real.pi) := by
      rw [Real.sq_sqrt]
      positivity
      all_goals norm_num
    have h2 : sqrt (Real.exp 1 / (Real.pi + Real.exp 1)) ^ 2 = Real.exp 1 / (Real.pi + Real.exp 1) := by
      rw [Real.sq_sqrt]
      positivity
      all_goals norm_num
    have h3 : sqrt (Real.pi / (Real.exp 1 + Real.pi)) * sqrt (Real.exp 1 / (Real.pi + Real.exp 1)) = Real.sqrt ((Real.pi / (Real.exp 1 + Real.pi)) * (Real.exp 1 / (Real.pi + Real.exp 1))) := by
      rw [← Real.sqrt_mul (by positivity)]
      all_goals norm_num
      all_goals norm_num
    have hpiexp : Real.pi / (Real.exp 1 + Real.pi) + Real.exp 1 / (Real.pi + Real.exp 1) = 1 := by
      have h_eq : Real.pi / (Real.exp 1 + Real.pi) + Real.exp 1 / (Real.pi + Real.exp 1) = 1 := by
        field_simp [(show Real.exp 1 + Real.pi ≠ 0 by positivity), (show Real.pi + Real.exp 1 ≠ 0 by positivity)]
        <;> ring
      linarith
    nlinarith [Real.sqrt_nonneg ((Real.pi / (Real.exp 1 + Real.pi)) * (Real.exp 1 / (Real.pi + Real.exp 1))), Real.sqrt_nonneg (Real.pi / (Real.exp 1 + Real.pi)), Real.sqrt_nonneg (Real.exp 1 / (Real.pi + Real.exp 1)), mul_nonneg (Real.sqrt_nonneg (Real.pi / (Real.exp 1 + Real.pi))) (Real.sqrt_nonneg (Real.exp 1 / (Real.pi + Real.exp 1))), h1, h2, Real.pi_pos, Real.exp_pos 1]
  rw [h_eq]
  all_goals norm_num
  all_goals norm_num
  all_goals norm_num
  all_goals norm_num
  all_goals positivity