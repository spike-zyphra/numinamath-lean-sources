import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_13459 : abs (1/2 - 3/8 * I) = 5/8 := by
  have h1 : abs (1 / 2 - 3 / 8 * I) = Real.sqrt ((1 / 2 : ℝ) ^ 2 + (-3 / 8 : ℝ) ^ 2) := by 
    simp [Complex.abs, Complex.normSq]
    <;> ring
  rw [h1]
  have h2 : Real.sqrt ((1 / 2 : ℝ) ^ 2 + (-3 / 8 : ℝ) ^ 2) = 5 / 8 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  exact h2