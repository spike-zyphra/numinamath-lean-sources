import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_321994 {z : ℂ} (hz : z = (4 + Real.sqrt 2 * .I) / (1 - .I)) :
    abs z = 3 := by 
  rw [hz]
  have h_abs : abs ((4 + Real.sqrt 2 * Complex.I) / (1 - Complex.I)) = abs (4 + Real.sqrt 2 * Complex.I) / abs (1 - Complex.I) := by 
    field_simp [Complex.abs]
  rw [h_abs]
  have h_abs1 : abs (4 + Real.sqrt 2 * Complex.I) = Real.sqrt 18 := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
    <;> norm_num
    all_goals ring_nf <;> norm_num
  have h_abs2 : abs (1 - Complex.I) = Real.sqrt 2 := by
    simp [Complex.abs, Complex.normSq]
    all_goals norm_num
  rw [h_abs1, h_abs2]
  have h : Real.sqrt 18 / Real.sqrt 2 = 3 := by
    have h1 : Real.sqrt 18 = Real.sqrt 9 * Real.sqrt 2 := by 
      rw [show (18 : ℝ) = 9 * 2 by norm_num]
      rw [Real.sqrt_mul (by norm_num)]
    have h2 : Real.sqrt 9 = 3 := by 
      rw [Real.sqrt_eq_cases]
      norm_num
    rw [h1, h2]
    field_simp
    <;> ring_nf <;> norm_num
  rw [h]
  all_goals norm_num