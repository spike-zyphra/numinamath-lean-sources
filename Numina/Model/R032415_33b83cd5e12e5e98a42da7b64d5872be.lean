import Mathlib

open Real Set
open scoped Real

theorem algebra_356061 {α β : ℝ} (hα : α ∈ Ioo 0 (π/2)) (hβ : β ∈ Ioo 0 (π/2))
    (h : sin β / sin α = cos (α + β)) :
    tan β = sin (2*α) / (3 - cos (2*α)) := by
  rcases hα with ⟨hα1, hα2⟩
  rcases hβ with ⟨hβ1, hβ2⟩
  have h1 : sin α ≠ 0 := by
    apply ne_of_gt
    apply sin_pos_of_pos_of_lt_pi
    linarith [hα1, hα2, Real.pi_pos]
    linarith [hα1, hα2, Real.pi_pos]

  have h2 : sin β = sin α * cos (α + β) := by 
    have h3 : sin β = sin α * cos (α + β) := by 
      field_simp [h1] at h ⊢
      linarith
    linarith
  have hcos : cos (α + β) = cos α * cos β - sin α * sin β := by 
    rw [cos_add]
  rw [hcos] at h2
  have h3 : sin β * (1 + sin α ^ 2) = sin α * cos α * cos β := by 
    nlinarith
  have hc1 : cos β ≠ 0 := by
    have h2 : β > 0 := hβ1
    have h3 : β < π / 2 := hβ2
    have h4 : cos β > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor <;> linarith [h2, h3, Real.pi_pos]
    nlinarith
  have htan : tan β = sin (2 * α) / (3 - cos (2 * α)) := by

    have h4 : tan β = sin β / cos β := by
      rw [tan_eq_sin_div_cos]
    have h5 : sin β / cos β = (sin α * cos α) / (1 + sin α ^ 2) := by

      have h6 : cos β ≠ 0 := hc1
      have h7 : 1 + sin α ^ 2 ≠ 0 := by
        nlinarith [show sin α ^ 2 ≥ 0 by positivity]

      field_simp [h6, h7] at *
      nlinarith [h3]
    rw [h4, h5]

    have h7 : sin (2 * α) = 2 * sin α * cos α := by
      rw [show 2 * α = 2 * α by rfl]
      rw [sin_two_mul]
    have h8 : cos (2 * α) = 1 - 2 * sin α ^ 2 := by
      rw [show 2 * α = 2 * α by rfl]
      rw [cos_two_mul]
      rw [sin_sq]
      all_goals ring
    have h9 : (3 - cos (2 * α) ) = 2 * (1 + sin α ^ 2) := by
      rw [h8]
      ring_nf
    have h7' : (sin α * cos α) / (1 + sin α ^ 2) = sin (2 * α) / (3 - cos (2 * α)) := by
      rw [h7, h9]

      have h10 : 1 + sin α ^ 2 ≠ 0 := by
        nlinarith [show sin α ^ 2 ≥ 0 by positivity]

      field_simp [h10, show 2 ≠ 0 by norm_num, show sin α ≠ 0 by assumption]
      <;> ring
    linarith
  exact htan