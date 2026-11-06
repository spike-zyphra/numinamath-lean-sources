import Mathlib

open Real Set
open scoped Real

theorem inequalities_153595 (α : ℝ) (hα : α ∈ Ioo 0 (π / 2)) :
    (1 + 1 / sin α) * (1 + 1 / cos α) > 5 := by
  rcases hα with ⟨h1, h2⟩
  have h3 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h1, h2, Real.pi_pos]
    linarith [h1, h2, Real.pi_pos]
  have h4 : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [h1, h2, Real.pi_pos]
    linarith [h1, h2, Real.pi_pos]
  have eq1 : (1 + 1 / sin α) * (1 + 1 / cos α) = 
    (sin α + cos α + 1) / (sin α * cos α) + 1 := by
    field_simp [h3, h4]
    <;> ring
  rw [eq1]
  have h1a : 0 < sin α * cos α := by
    have h71 : 0 < sin α := h3
    have h72 : 0 < cos α := h4
    nlinarith
  have h5 : (sin α + cos α + 1) / (sin α * cos α) > 4 := by
    have h3a : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    have h7 : 0 < α := h1
    have h8 : α < Real.pi / 2 := h2
    have h9 : sin α > 0 := h3
    have h10 : cos α > 0 := h4
    have h1a1 : sin α * cos α > 0 := by
      nlinarith 
    have h11 : sin α + cos α > 1 := by
      nlinarith [ sq_pos_of_pos h3, sq_pos_of_pos h4, Real.sin_sq_add_cos_sq α, sq_nonneg (sin α - cos α), sq_nonneg (sin α + cos α - 1) ]
    have h12 : sin α * cos α > 0 := h1a1 
    have h6f : sin α + cos α + 1 > 4 * (sin α * cos α) := by 
      nlinarith [sq_nonneg (sin α - cos α), sq_nonneg (sin α + cos α - 1), sq_nonneg (sin α ^ 2 - cos α ^ 2), Real.sin_sq_add_cos_sq α, mul_pos h3 h4, sq_pos_of_pos h3, sq_pos_of_pos h4]
    have h6f' : (sin α + cos α + 1) / (sin α * cos α) > 4 := by
      have h3a : sin α * cos α > 0 := h1a
      apply (lt_div_iff₀ h3a).mpr 
      linarith [h6f]
    linarith [h6f']
  linarith [h5]