import Mathlib

open Real Set
open scoped Real

theorem algebra_279993 (α : Real) (hα : α ∈ Ioo 0 (π / 4)) :
    tan (2 * α) / tan α = 1 + 1 / cos (2 * α) := by
  rcases hα with ⟨hα1, hα2⟩
  have h1 : α > 0 := hα1
  have h2 : α < Real.pi / 4 := hα2
  have h3 : 2 * α < Real.pi / 2 := by
    linarith [Real.pi_pos, h2]
  have hsin : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos, h2]
  have hcos : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos]
    linarith [Real.pi_pos, h2]
  have hcos2 : cos (2 * α) > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · -- Show -π/2 < 2*α
      linarith [Real.pi_pos, h1]
    · -- Show 2*α < π/2
      linarith [Real.pi_pos, h3]
  have htan_ne_zero : tan α ≠ 0 := by
    rw [tan_eq_sin_div_cos]
    apply div_ne_zero
    · -- Show sin α ≠ 0
      by_contra h
      have : sin α = 0 := by linarith
      linarith
    · -- Show cos α ≠ 0
      by_contra h
      have : cos α = 0 := by linarith
      linarith
  have htan2_ne_zero : cos (2 * α) ≠ 0 := by linarith [hcos2]
  have htan_eq : tan (2 * α) = sin (2 * α) / cos (2 * α) := by
    rw [tan_eq_sin_div_cos]
  have htanα_eq : tan α = sin α / cos α := by
    rw [tan_eq_sin_div_cos]
  have hsin2α_eq : sin (2 * α) = 2 * sin α * cos α := by
    rw [sin_two_mul]
  rw [htan_eq, htanα_eq, hsin2α_eq]
  field_simp [htan_ne_zero, hcos, hsin, htan2_ne_zero, hcos2, hsin, hcos]
  <;> rw [cos_two_mul] <;> nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq (2 * α), sq_pos_of_pos hsin, sq_pos_of_pos hcos, sq_pos_of_pos hcos2]