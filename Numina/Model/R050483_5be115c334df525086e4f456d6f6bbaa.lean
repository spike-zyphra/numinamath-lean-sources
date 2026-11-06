import Mathlib

open Real Set
open scoped Real

theorem calculus_15306 (θ : ℝ) (hθ : θ = arcsin (2 / 3)) :
    cos θ = sqrt 5 / 3 := by 
  rw [hθ]
  have h2 : cos (arcsin (2 / 3 : ℝ)) = Real.sqrt (1 - (2 / 3 : ℝ) ^ 2) := by 
    rw [cos_arcsin]
    all_goals norm_num
  rw [h2]
  have h3 : Real.sqrt (1 - (2 / 3 : ℝ) ^ 2) = Real.sqrt 5 / 3 := by 
    rw [show (1 - (2 / 3 : ℝ) ^ 2) = (5 / 9 : ℝ) by norm_num]
    have h4 : Real.sqrt ((5 / 9 : ℝ)) = Real.sqrt 5 / Real.sqrt 9 := by 
      field_simp [Real.sqrt_div]
      all_goals norm_num
    have h5 : Real.sqrt (9 : ℝ) = 3 := by 
      rw [Real.sqrt_eq_cases]
      norm_num
    rw [h4]
    rw [h5]
    <;> ring_nf <;> norm_num [Real.sqrt_mul_self]
    all_goals norm_num
  rw [h3]
  <;> ring_nf <;> norm_num [Real.sqrt_mul_self]
  all_goals norm_num
  <;> norm_num
  <;> ring_nf
  <;> norm_num