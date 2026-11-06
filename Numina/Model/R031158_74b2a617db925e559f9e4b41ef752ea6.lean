import Mathlib

open Real

theorem algebra_185416 (α : ℝ) (h : sin (2 * α) ≠ 0) :
    cos (4 * α) - sin (4 * α) * cot (2 * α) = cos (2 * α) - 2 * cos α ^ 2 := by
  have hcot : cot (2 * α) = cos (2 * α) / sin (2 * α) := by
    rw [cot_eq_cos_div_sin]
  rw [hcot]
  have eq1 : cos (4 * α) - sin (4 * α) * (cos (2 * α) / sin (2 * α)) =
      (cos (4 * α) * sin (2 * α) - sin (4 * α) * cos (2 * α)) / sin (2 * α) := by
    field_simp [h]
    <;> ring
  rw [eq1]
  have eq2 : cos (4 * α) * sin (2 * α) - sin (4 * α) * cos (2 * α) = - sin (2 * α) := by
    have h1 : sin (4 * α) = 2 * sin (2 * α) * cos (2 * α) := by
      have h2 : sin (4 * α) = sin (2 * (2 * α)) := by ring_nf
      rw [h2]
      rw [sin_two_mul]
      all_goals ring
    have h2 : cos (4 * α) = 2 * cos (2 * α) ^ 2 - 1 := by
      have h3 : cos (4 * α) = cos (2 * (2 * α)) := by ring_nf
      rw [h3]
      rw [cos_two_mul]
    rw [h1, h2]
    have eq3 : (2 * cos (2 * α) ^ 2 - 1) * sin (2 * α) - (2 * sin (2 * α) * cos (2 * α)) * cos (2 * α) =
          - sin (2 * α) := by
      have eq4 : (2 * cos (2 * α) ^ 2 - 1) * sin (2 * α) - (2 * sin (2 * α) * cos (2 * α)) * cos (2 * α) =
          2 * cos (2 * α) ^ 2 * sin (2 * α) - sin (2 * α) - 2 * sin (2 * α) * cos (2 * α) ^ 2 := by
        ring
      rw [eq4]
      ring_nf
    linarith
  have eq3 : sin (2 * α) ≠ 0 := h 
  rw [eq2]
  field_simp [h]
  have eq4 : cos (2 * α) - 2 * cos α ^ 2 = -1 := by
    have h4 : cos (2 * α) = 2 * cos α ^ 2 - 1 := by
      rw [cos_two_mul]
    rw [h4]
    linarith
  linarith [eq4]