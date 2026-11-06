import Mathlib

open Real Set
open scoped Real

theorem inequalities_45903 (α : Real) (hα : α ∈ Ioo 0 (π / 2)) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b / sin α) * (b + a / cos α) ≥ a ^ 2 + b ^ 2 + 3 * a * b := by
  rcases hα with ⟨h1, h2⟩
  have h3 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h1, h2, Real.pi_pos]
    linarith [h1, h2, Real.pi_pos]
  have h4 : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [h1, h2, Real.pi_pos]
  have h5 : sin α * cos α > 0 := mul_pos h3 h4
  have h6 : (a + b / sin α) * (b + a / cos α) = a * b + a ^ 2 / cos α + b ^ 2 / sin α + a * b / (sin α * cos α) := by
    field_simp
    ring
  rw [h6]
  have h7 : a ^ 2 / cos α ≥ a ^ 2 := by
    have h8 : cos α ≤ 1 := by
      nlinarith [Real.cos_sq_add_sin_sq α, sq_nonneg (cos α - 1)]
    have h9 : cos α > 0 := h4
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg a]
  have h8 : b ^ 2 / sin α ≥ b ^ 2 := by
    have h9 : sin α ≤ 1 := by
      nlinarith [Real.cos_sq_add_sin_sq α, sq_nonneg (sin α - 1)]
    have h10 : sin α > 0 := h3
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg b]
  have h12 : a * b / (sin α * cos α) ≥ 2 * a * b := by
    have h10 : sin α * cos α ≤ 1 / 2 := by
      nlinarith [sq_nonneg (sin α - cos α), Real.cos_sq_add_sin_sq α, mul_pos h3 h4]
    have h11 : sin α * cos α > 0 := h5
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg ha hb]
  nlinarith [h7, h8, h12, mul_self_nonneg (a - b), mul_self_nonneg (sin α - 1 / 2), mul_self_nonneg (cos α - 1 / 2), Real.sin_pos_of_pos_of_lt_pi (show 0 < α by linarith) (show α < Real.pi by linarith [h1, h2, Real.pi_pos]), Real.cos_pos_of_mem_Ioo (show α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [h1, h2, Real.pi_pos]), mul_nonneg ha hb]