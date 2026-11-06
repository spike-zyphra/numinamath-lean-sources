import Mathlib

open Real Set
open scoped Real

theorem algebra_356061 {α β : ℝ} (hα : α ∈ Ioo 0 (π/2)) (hβ : β ∈ Ioo 0 (π/2))
    (h : sin β / sin α = cos (α + β)) :
    tan β = sin (2*α) / (3 - cos (2*α)) := by
  have h1 : tan β = sin (2 * α) / (3 - cos (2 * α)) := by
    have hα1 : 0 < α := hα.left
    have hα2 : α < π / 2 := hα.right
    have hβ1 : 0 < β := hβ.left
    have hβ2 : β < π / 2 := hβ.right
    have hsinα_ne_zero : sin α ≠ 0 := by
      apply ne_of_gt
      apply sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [Real.pi_pos]
    have eq1 : sin β = sin α * cos (α + β) := by
      have h' : sin β = sin α * (cos (α + β)) := by
        field_simp [hsinα_ne_zero] at h
        linarith
      exact h'
    rw [cos_add] at eq1
    have eq2 : sin β * (1 + sin α ^ 2) = sin α * cos α * cos β := by
      linarith [eq1]
    have hcosβ_ne_zero : cos β ≠ 0 := by
      have hcosβ_pos : cos β > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor <;> linarith [Real.pi_pos]
      by_contra h
      have : cos β = 0 := by linarith
      linarith [hcosβ_pos, this]
    have eq3 : tan β = sin α * cos α / (1 + sin α ^ 2) := by
      have eq3 : tan β = sin β / cos β := by
        rw [tan_eq_sin_div_cos]
      have eq4 : sin β / cos β = sin α * cos α / (1 + sin α ^ 2) := by
        field_simp
        linarith [eq2]
      rw [eq3, eq4]
    have eq4 : tan β = sin (2 * α) / (3 - cos (2 * α)) := by
      have eq6 : sin (2 * α) = 2 * sin α * cos α := sin_two_mul α
      have eq7 : cos (2 * α) = 2 * cos α ^ 2 - 1 := cos_two_mul α
      have eq8 : 1 + sin α ^ 2 = (3 - cos (2 * α)) / 2 := by
        have h1 : cos (2 * α) = 2 * cos α ^ 2 - 1 := eq7
        have h2 : cos α ^ 2 = 1 - sin α ^ 2 := by
          exact cos_sq' α
        linarith
      have eq9 : sin α * cos α = sin (2 * α) / 2 := by
        linarith
      rw [eq3]
      have h2 : sin (2 * α) / 2 / ((3 - cos (2 * α)) / 2) = sin (2 * α) / (3 - cos (2 * α)) := by
        field_simp
      rw [eq9]
      rw [eq8]
      field_simp
    exact eq4
  exact h1