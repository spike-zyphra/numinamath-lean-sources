import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_160824 {z : ℂ} (hz : z = ((2 + I)^2) / (1 - I)) :
    z.re < 0 ∧ z.im > 0 := by 
  rw [hz]
  have h1 : ((2 + Complex.I):ℂ) ^ 2 / (1 - Complex.I) = (-1/2 : ℂ) + (7/2) * Complex.I := by
    field_simp [Complex.ext_iff, Complex.I_mul_I, pow_two]
    all_goals norm_num
  rw [h1]
  constructor
  · norm_num
  · norm_num