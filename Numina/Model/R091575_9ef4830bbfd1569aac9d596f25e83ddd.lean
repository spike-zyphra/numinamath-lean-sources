import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem calculus_22251 : abs (4 + 2 * I) * abs (6 - 3 * I) = 30 := by
  have h1 : abs (4 + 2 * I) = Real.sqrt 20 := by
    simp [Complex.abs, Complex.normSq]
    all_goals norm_num
  have h2 : abs (6 - 3 * I) = Real.sqrt 45 := by
    simp [Complex.abs, Complex.normSq]
    all_goals norm_num
  rw [h1, h2]
  have h3 : Real.sqrt 20 * Real.sqrt 45 = Real.sqrt (20 * 45) := by
    rw [← Real.sqrt_mul (by norm_num)]
  have h4 : Real.sqrt (20 * 45) = 30 := by
    norm_num [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h3, h4]