import Mathlib

open Real Set
open scoped Real

theorem algebra_181023 :
  sin (arcsin (3/5) + arccos (1/3)) = (3 + 8*sqrt 2)/15 := by
  have h1 : sin (arcsin (3 / 5)) = 3 / 5 := by
    apply sin_arcsin
    all_goals norm_num
  have h2 : cos (arccos (1 / 3)) = 1 / 3 := by 
    apply cos_arccos
    all_goals norm_num
  have h3 : cos (arcsin (3 / 5)) = 4 / 5 := by 
    have h4 : cos (arcsin (3 / 5)) = Real.sqrt (1 - (3 / 5) ^ 2) := by
      rw [cos_arcsin]
    rw [h4]
    have h5 : (3 / 5 : ℝ) ^ 2 = 9 / 25 := by norm_num
    rw [h5]
    have h6 : (1 : ℝ) - (9 / 25 : ℝ) = 16 / 25 := by norm_num
    rw [h6]
    have h7 : Real.sqrt ((16 / 25 : ℝ)) = 4 / 5 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h7]
  have h8 : sin (arccos (1 / 3)) = 2 * Real.sqrt 2 / 3 := by 
    have h9 : sin (arccos (1 / 3)) = Real.sqrt (1 - (1 / 3) ^ 2) := by
      rw [sin_arccos]
    rw [h9]
    have h10 : (1 / 3 : ℝ) ^ 2 = 1 / 9 := by norm_num
    rw [h10]
    have h11 : (1 : ℝ) - (1 / 9 : ℝ) = 8 / 9 := by norm_num
    rw [h11]
    have h12 : Real.sqrt ((8 / 9 : ℝ)) = 2 * Real.sqrt 2 / 3 := by 
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h12]
    all_goals norm_num
  rw [sin_add]
  rw [h1, h2, h3, h8]
  field_simp
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num
  all_goals ring