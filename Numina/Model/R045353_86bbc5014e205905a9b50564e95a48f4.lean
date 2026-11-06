import Mathlib

open Real Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_253234 : ((1 + I * Real.sqrt 3) / 2) ^ 60 + ((1 - I * Real.sqrt 3) / 2) ^ 30 = 2 := by
  have h1 : ((1 + I * Real.sqrt 3) / 2) ^ 3 = -1 := by
    simp [pow_three]
    field_simp [Complex.ext_iff, mul_add, pow_two, mul_assoc, Complex.I_mul_I, pow_three]
    ring_nf
    <;> norm_num [Real.sqrt_sq]
    <;> ring_nf
    <;> norm_num [Complex.I_sq]
    <;> ring
  have h2 : ((1 - I * Real.sqrt 3) / 2) ^ 3 = -1 := by
    simp [pow_three]
    field_simp [Complex.ext_iff, mul_add, pow_two, mul_assoc, Complex.I_mul_I, pow_three]
    ring_nf
    <;> norm_num [Real.sqrt_sq]
    <;> ring_nf
    <;> norm_num [Complex.I_sq]
    <;> ring
  have h3 : ((1 + I * Real.sqrt 3) / 2) ^ 60 = 1 := by
    calc
      ((1 + I * Real.sqrt 3) / 2) ^ 60 = (( (1 + I * Real.sqrt 3) / 2) ^ 3) ^ 20 := by ring
      _ = (-1) ^ 20 := by rw [h1]
      _ = 1 := by norm_num
  have h4 : ((1 - I * Real.sqrt 3) / 2) ^ 30 = 1 := by
    calc
      ((1 - I * Real.sqrt 3) / 2) ^ 30 = (( (1 - I * Real.sqrt 3) / 2) ^ 3) ^ 10 := by ring
      _ = (-1) ^ 10 := by rw [h2]
      _ = 1 := by norm_num
  rw [h3, h4]
  norm_num
  <;> ring_nf
  <;> norm_num [Complex.I_sq]
  <;> ring