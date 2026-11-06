import Mathlib

open Real
open scoped Real

theorem inequalities_190542 (A B C : Real) (hA : A ∈ Set.Ioo 0 π)
  (hB : B ∈ Set.Ioo 0 π) (hC : C ∈ Set.Ioo 0 π) (hABC : A + B + C = π) :
  3 / 2 ≤ sin (B + C) / (sin B + sin C) + sin (C + A) / (sin C + sin A) +
    sin (A + B) / (sin A + sin B) := by
  have h1 : sin (B + C) = sin A := by
    have h2 : B + C = π - A := by 
      linarith
    rw [h2]
    rw [sin_pi_sub]
  have h2 : sin (C + A) = sin B := by 
    have h3 : C + A = π - B := by 
      linarith
    rw [h3]
    rw [sin_pi_sub]
  have h3 : sin (A + B) = sin C := by
    have h4 : A + B = π - C := by 
      linarith 
    rw [h4]
    rw [sin_pi_sub]
  rw [h1, h2, h3]
  have h4 : sin A > 0 := by
    have hA1 : 0 < A := hA.1
    have hA2 : A < π := hA.2
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have h5 : sin B > 0 := by 
    have hB1 : 0 < B := hB.1
    have hB2 : B < π := hB.2
    apply sin_pos_of_pos_of_lt_pi 
    linarith 
    linarith 
  have h6 : sin C > 0 := by 
    have hC1 : 0 < C := hC.1
    have hC2 : C < π := hC.2
    apply sin_pos_of_pos_of_lt_pi 
    linarith 
    linarith 
  have h7 : sin B + sin C > 0 := by 
    linarith 
  have h8 : sin C + sin A > 0 := by
    linarith 
  have h9 : sin A + sin B > 0 := by
    linarith 
  have h11 : sin A / (sin B + sin C) + sin B / (sin C + sin A) + 
          sin C / (sin A + sin B) - 3 / 2 ≥ 0 := by 
    have h14 : sin A / (sin B + sin C) + sin B / (sin C + sin A) + sin C / (sin A + sin B) - 3 / 2 =
        (2 * sin A * (sin C + sin A) * (sin A + sin B) + 2 * sin B * (sin B + sin C) * (sin A + sin B) + 2 * sin C * (sin B + sin C) * (sin C + sin A) - 3 * (sin B + sin C) * (sin C + sin A) * (sin A + sin B)) / (2 * (sin B + sin C) * (sin C + sin A) * (sin A + sin B)) := by 
      field_simp
      ring 
    rw [h14] 
    apply div_nonneg
    nlinarith [sq_nonneg (sin A - sin B), sq_nonneg (sin B - sin C), sq_nonneg (sin C - sin A), 
          mul_pos h4 h5, mul_pos h5 h6, mul_pos h4 h6, 
          sq_nonneg (sin A^2 - sin B^2), sq_nonneg (sin B^2 - sin C^2), sq_nonneg (sin C^2 - sin A^2)]
    positivity 
  linarith [h11]