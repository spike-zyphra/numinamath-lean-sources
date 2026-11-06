import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_21972 : abs ((2 - 4 * I) / (2 + I)) = 2 := by
  have h1 : abs ((2 - 4 * I) / (2 + I)) = abs (2 - 4 * I) / abs (2 + I) := by
    field_simp [Complex.abs]
    <;> norm_num [Complex.normSq]
    <;> ring_nf <;> norm_num [Complex.normSq]
  have h2 : abs (2 - 4 * I) = Real.sqrt 20 := by
    simp [Complex.abs, Complex.normSq]
    all_goals norm_num
    <;> ring_nf <;> norm_num [Complex.normSq]
  have h3 : abs (2 + I) = Real.sqrt 5 := by
    simp [Complex.abs, Complex.normSq]
    all_goals norm_num
    <;> ring_nf <;> norm_num [Complex.normSq]
  rw [h1, h2, h3]
  have h4 : Real.sqrt 20 / Real.sqrt 5 = 2 := by
    have h5 : Real.sqrt 20 = Real.sqrt (4 * 5) := by
      norm_num
    have h6 : Real.sqrt (4 * 5) = Real.sqrt 4 * Real.sqrt 5 := by
      rw [Real.sqrt_mul]
      all_goals norm_num
    have h7 : Real.sqrt 4 = (2 : ℝ) := by
      rw [Real.sqrt_eq_cases]
      all_goals norm_num
    rw [h5, h6, h7]
    field_simp
    <;> ring_nf <;> norm_num [Real.sqrt_sq]
  rw [h4]
  all_goals norm_num