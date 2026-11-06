import Mathlib

theorem algebra_182801 (α : ℝ) (h₀ : α ∈ Set.Ioo 0 Real.pi) (h₁ : Real.sin α + Real.cos α = -1 / 5) :
    Real.tan α = -3 / 4 := by
  rw [Set.mem_Ioo] at h₀
  have h2 : 0 < α := h₀.1
  have h3 : α < Real.pi := h₀.2
  have h4 : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi h2 (by linarith [Real.pi_gt_three])
  have h5 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h6 : (Real.sin α + Real.cos α) ^ 2 = ( -1 / 5 ) ^ 2 := by 
    rw [h₁]
  have h7 : (Real.sin α + Real.cos α) ^ 2 = Real.sin α ^ 2 + Real.cos α ^ 2 + 2 * (Real.sin α * Real.cos α) := by 
    ring
  rw [h7] at h6
  rw [h5] at h6
  have h8 : Real.sin α * Real.cos α = -12 / 25 := by
    nlinarith
  have h9 : Real.sin α = 3 / 5 := by
    nlinarith [h₁, h8, h4]
  have h10 : Real.cos α = -4 / 5 := by
    nlinarith [h₁, h9]
  rw [Real.tan_eq_sin_div_cos]
  rw [h9, h10]
  all_goals norm_num