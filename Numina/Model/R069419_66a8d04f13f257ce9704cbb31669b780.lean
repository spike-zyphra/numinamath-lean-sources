import Mathlib

theorem algebra_308307 (α : Real) (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) (h : 3 * Real.sin α + 4 * Real.cos α = 5) :
    Real.tan α = 3 / 4 := by
  rcases hα with ⟨h₁, h₂⟩
  have h3 : Real.sin α > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h4 : Real.cos α > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h5 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h6 : Real.sin α = (5 - 4 * Real.cos α) / 3 := by
    linarith
  rw [h6] at h5
  have h7 : 25 * (Real.cos α) ^ 2 - 40 * (Real.cos α) + 16 = 0 := by
    nlinarith
  have h8 : (Real.cos α - 4 / 5) ^ 2 = 0 := by
    nlinarith [h7]
  have h9 : Real.cos α = 4 / 5 := by
    nlinarith
  have h10 : Real.sin α = 3 / 5 := by
    rw [h9] at h6
    linarith
  rw [Real.tan_eq_sin_div_cos, h10, h9]
  all_goals norm_num