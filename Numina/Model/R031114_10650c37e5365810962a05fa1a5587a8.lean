import Mathlib

open Real

theorem calculus_17066 {a b : ℝ} (h : 5 * (cos a + cos b) + 4 * (cos a * cos b + 1) = 0)
(ha: cos (a / 2) ≠ 0)(hb : cos (b / 2) ≠ 0):
tan (a / 2) * tan (b / 2) = 3 ∨ tan (a / 2) * tan (b / 2) = -3 := by
  have h_eq : 5 * (cos a + cos b) + 4 * (cos a * cos b + 1) = 0 := h 
  have h1 : cos a = (1 - tan (a / 2) ^ 2) / (1 + tan (a / 2) ^ 2) := by 
    have htan : cos (a / 2) ≠ 0 := ha
    have ha1 : tan (a / 2) = sin (a / 2) / cos (a / 2) := by 
      rw [tan_eq_sin_div_cos]
    have h2 : cos a = 2 * cos (a / 2) ^ 2 - 1 := by 
      have h1 : cos a = cos (2 * (a / 2)) := by ring_nf
      rw [h1]
      rw [cos_two_mul]
      <;> try tauto
    have htan2 : tan (a / 2) ^ 2 = (sin (a / 2) ^ 2) / (cos (a / 2) ^ 2) := by
      rw [tan_eq_sin_div_cos]
      have : cos (a / 2) ≠ 0 := ha
      field_simp
    have h34 : sin (a / 2) ^ 2 = 1 - cos (a / 2) ^ 2 := by
      have : sin (a / 2) ^ 2 + cos (a / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (a / 2)
      linarith 
    field_simp [htan2, h34, show cos (a / 2) ≠ 0 by exact ha] at htan2 ⊢
    nlinarith [Real.sin_sq_add_cos_sq (a/2), sq_pos_of_ne_zero (show cos (a / 2) ≠ 0 from ha)]
  have h2 : cos b = (1 - tan (b / 2) ^ 2) / (1 + tan (b / 2) ^ 2) := by 
    have htan : cos (b / 2) ≠ 0 := hb
    have hb1 : tan (b / 2) = sin (b / 2) / cos (b / 2) := by 
      rw [tan_eq_sin_div_cos]
    have h3 : cos b = 2 * cos (b / 2) ^ 2 - 1 := by 
      have h1 : cos b = cos (2 * (b / 2)) := by ring_nf
      rw [h1]
      rw [cos_two_mul]
      <;> try tauto
    have htan2 : tan (b / 2) ^ 2 = (sin (b / 2) ^ 2) / (cos (b / 2) ^ 2) := by 
      rw [tan_eq_sin_div_cos]
      have : cos (b / 2) ≠ 0 := hb
      field_simp
    have h34 : sin (b / 2) ^ 2 = 1 - cos (b / 2) ^ 2 := by 
      have : sin (b / 2) ^ 2 + cos (b / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (b / 2)
      linarith
    field_simp [htan2, h34, show cos (b / 2) ≠ 0 by exact hb] at htan2 ⊢
    nlinarith [Real.sin_sq_add_cos_sq (b/2), sq_pos_of_ne_zero (show cos (b / 2) ≠ 0 from hb)]
  have h32 : (tan (a / 2) * tan (b / 2) + 3) * (tan (a / 2) * tan (b / 2) - 3) = 0 := by 
    have ht := h_eq
    rw [h1, h2] at ht
    field_simp [(show 1 + tan (a / 2) ^ 2 ≠ 0 by positivity), 
            (show 1 + tan (b / 2) ^ 2 ≠ 0 by positivity)] at ht ⊢
    ring_nf at ht ⊢
    nlinarith [sq_nonneg (tan (a / 2) * tan (b / 2) ), sq_nonneg (tan (a / 2) ^ 2 - 3), 
       sq_nonneg (tan (b / 2) ^ 2 - 3), sq_nonneg (tan (a / 2) ), sq_nonneg (tan (b / 2) ), 
       sq_nonneg (tan (a / 2) - tan (b / 2) ), sq_nonneg (tan (a / 2) + tan (b / 2) )
    ]
  cases' (mul_eq_zero.mp h32) with h33 h34
  · -- Show that tan(a/2) * tan(b/2) = -3
    right
    linarith 
  · -- Show that tan(a/2) * tan (b/2) = 3
    left
    linarith