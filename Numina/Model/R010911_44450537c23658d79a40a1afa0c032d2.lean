import Mathlib

open Real Set
open scoped Real

theorem calculus_22045 {A B : ℝ} (hA : cos (A + B) ≠ 0) (hB : sin B ≠ 0) (hC : sin A ≠ 0)
  (h : sin (2 * A + B) / sin B = 5) :
  tan (A + B) / tan A = 3 / 2 := by
  have h1 : 5 * sin B = sin (2 * A + B) := by 
    have h2 : sin (2 * A + B) = 5 * sin B := by
      field_simp [hB] at h ⊢
      linarith
    linarith [h2]
  have eq1 : sin (2 * A + B) = sin (A + B) * cos A + cos (A + B) * sin A := by 
    rw [show 2 * A + B = (A + B) + A by ring]
    rw [sin_add]
  have eq2 : sin B = sin (A + B) * cos A - cos (A + B) * sin A := by 
    have eq3 : sin B = sin ((A + B) - A) := by 
      ring_nf
    rw [eq3]
    rw [sin_sub]
    <;> ring
  rw [eq1, eq2] at h1
  have h2 : 2 * sin (A + B) * cos A - 3 * cos (A + B) * sin A = 0 := by
    linarith
  have htan1 : tan (A + B) = sin (A + B) / cos (A + B) := by 
    rw [tan_eq_sin_div_cos]
  have htan2 : tan A = sin A / cos A := by 
    rw [tan_eq_sin_div_cos]
  have htan : tan (A + B) / tan A = 3 / 2 := by
    rw [htan1, htan2]
    have h3 : cos (A + B) ≠ 0 := hA
    have h4 : sin A ≠ 0 := hC
    field_simp [h3, h4]
    linarith [h2]
  exact htan