import Mathlib

open Real Set
open scoped Real

theorem calculus_17053 :
  sin (arcsin (3/5) + arctan 2) = (11*sqrt 5)/25 := by
  have h1 : sin (arcsin (3/5) + arctan 2) =
    sin (arcsin (3/5)) * cos (arctan 2) + cos (arcsin (3/5)) * sin (arctan 2) := by
    rw [sin_add]
  have h2 : sin (arcsin (3 / 5)) = 3 / 5 := by
    apply sin_arcsin
    all_goals norm_num
  have h3 : cos (arcsin (3 / 5)) = 4 / 5 := by
    have h4 : cos (arcsin (3/5)) = Real.sqrt (1 - (3/5)^2) := by
      rw [cos_arcsin]
      <;> ring_nf
      all_goals norm_num
    rw [h4]
    have h5 : Real.sqrt (1 - (3/5)^2) = 4/5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    rw [h5]
  have h6 : sin (arctan 2) = 2 * Real.sqrt 5 / 5 := by
    rw [sin_arctan]
    have h7 : Real.sqrt (1 + (2:ℝ)^2) = Real.sqrt 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
      all_goals linarith
    rw [h7]
    field_simp
    <;> ring_nf
    <;> norm_num
    all_goals linarith
    all_goals norm_num
  have h8 : cos (arctan 2) = Real.sqrt 5 / 5 := by
    rw [cos_arctan]
    have h9 : Real.sqrt (1 + (2:ℝ)^2) = Real.sqrt 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
      all_goals linarith
    rw [h9]
    field_simp
    <;> ring_nf
    <;> norm_num
    all_goals linarith
    all_goals norm_num
  rw [h1, h2, h3, h6, h8]
  have h9 : Real.sqrt 5 ^ 2 = 5 := by
    rw [Real.sq_sqrt]
    all_goals norm_num
  field_simp
  nlinarith [Real.sqrt_nonneg 5, h9]
  all_goals linarith
  all_goals norm_num
  all_goals linarith