import Mathlib

open Real
open scoped BigOperators

theorem algebra_153924 (A B C : EuclideanSpace ℝ (Fin 3))
  (hA : A = ![0, 0, 4]) (hB : B = ![-3, -6, 1]) (hC : C = ![-5, -10, -1]) :
  let v1 := B - A
  let v2 := C - A
  let cosθ := (inner v1 v2) / (norm v1 * norm v2)
  cosθ = 1 := by 
  simp [hA, hB, hC]
  simp [Fin.sum_univ_three, inner, EuclideanSpace.norm_eq, Matrix.sum_apply]
  ring_nf
  have h1 : Real.sqrt 54 * Real.sqrt 150 = (90 : ℝ) := by 
    have h2 : Real.sqrt 54 * Real.sqrt 150 = Real.sqrt (54 * (150 : ℝ)) := by 
      rw [← Real.sqrt_mul (by norm_num)]
    rw [h2]
    rw [show (54 * (150 : ℝ) : ℝ) = 8100 by norm_num]
    have h3 : Real.sqrt (8100 : ℝ) = (90 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> linarith
    rw [h3]
    <;> norm_num
    <;> ring_nf <;> norm_num
  have h4 : (Real.sqrt 54)⁻¹ * (Real.sqrt 150)⁻¹ * (90 : ℝ) = 1 := by 
    have h2 : Real.sqrt 54 * Real.sqrt 150 = (90 : ℝ) := h1
    have h5 : (Real.sqrt 54)⁻¹ * (Real.sqrt 150)⁻¹ = (Real.sqrt 54 * Real.sqrt 150)⁻¹ := by 
      field_simp 
      <;> ring_nf <;> norm_num
    have h6 : (Real.sqrt 54 * Real.sqrt 150)⁻¹ = (90 : ℝ)⁻¹ := by 
      rw [h2]
    have h7 : (90 : ℝ)⁻¹ * (90 : ℝ) = 1 := by 
      field_simp 
      <;> norm_num
    calc 
      (Real.sqrt 54)⁻¹ * (Real.sqrt 150)⁻¹ * (90 : ℝ)
          = ( (Real.sqrt 54 * Real.sqrt 150)⁻¹ ) * (90 : ℝ) := by rw [h5]
      _ = ( (90 : ℝ)⁻¹ ) * (90 : ℝ) := by rw [h6]
      _ = 1 := by rw [h7]
  norm_num [h4]
  <;> ring_nf <;> norm_num [Real.sqrt_nonneg]
  <;> ring
  <;> norm_num
  <;> try { ring }
  <;> try { norm_num [Real.sqrt_nonneg] }