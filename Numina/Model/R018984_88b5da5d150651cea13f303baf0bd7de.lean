import Mathlib

open Real Set
open scoped Real

theorem algebra_297156 (α β : ℝ) (h₀ : sin (α + 2 * β) = 3 / 5)
  (h₁ : sin (2 * α - 3 * β) = 4 / 5) (h₂ : α ∈ Icc (π / 12) (π / 4))
  (h₃ : β ∈ Icc 0 (π / 12)) :
  sin (8 * α - 5 * β) = -4 / 5 := by
  rcases h₂ with ⟨h₂₁, h₂₂⟩
  rcases h₃ with ⟨h₃₁, h₃₂⟩
  have h4 : cos (α + 2 * β) > 0 := by
    have h5 : 0 < α + 2 * β := by 
      linarith [h₂₁, h₃₁, Real.pi_pos]
    have h6 : α + 2 * β < Real.pi / 2 := by 
      nlinarith [h₂₂, h₃₂, Real.pi_pos]
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith
  -- Calculate cos(α + 2β)
  have h7 : cos (α + 2 * β) = 4 / 5 := by
    have h8 : cos (α + 2 * β) ^ 2 + sin (α + 2 * β) ^ 2 = 1 := Real.cos_sq_add_sin_sq (α + 2 * β)
    rw [h₀] at h8
    have h9 : cos (α + 2 * β) > 0 := h4
    nlinarith [h9]
  -- Calculate sin(2(α + 2β))
  have h10 : sin (2 * (α + 2 * β)) = 24 / 25 := by 
    have h11 : sin (2 * (α + 2 * β)) = 2 * sin (α + 2 * β) * cos (α + 2 * β) := by
      rw [sin_two_mul]
    rw [h11, h₀, h7]
    norm_num
  -- Calculate cos(2(α + 2β))
  have h12 : cos (2 * (α + 2 * β)) = 7 / 25 := by 
    have h13 : cos (2 * (α + 2 * β)) = 1 - 2 * sin (α + 2 * β) ^ 2 := by
      rw [cos_two_mul, sin_sq]
      all_goals ring
    rw [h13, h₀]
    norm_num
  -- Show cos(2α - 3β) ≥ 0
  have h14 : cos (2 * α - 3 * β) ≥ 0 := by 
    have h15 : -(Real.pi / 12) ≤ 2 * α - 3 * β := by 
      nlinarith [h₂₁, h₃₂, Real.pi_pos]
    have h16 : 2 * α - 3 * β ≤ Real.pi / 2 := by 
      nlinarith [h₂₂, h₃₁, Real.pi_pos]
    apply cos_nonneg_of_neg_pi_div_two_le_of_le 
    all_goals nlinarith [Real.pi_pos]
  -- Calculate cos(2α - 3β)
  have h17 : cos (2 * α - 3 * β) = 3 / 5 := by 
    have h18 : cos (2 * α - 3 * β) ^ 2 + sin (2 * α - 3 * β) ^ 2 = 1 := Real.cos_sq_add_sin_sq (2 * α - 3 * β)
    rw [h₁] at h18
    nlinarith [h14]
  -- Calculate sin(3(2α - 3β))
  have h18 : sin (3 * (2 * α - 3 * β)) = 44 / 125 := by 
    have h19 : sin (3 * (2 * α - 3 * β)) = 3 * sin (2 * α - 3 * β) - 4 * sin (2 * α - 3 * β) ^ 3 := by 
      rw [sin_three_mul]
    rw [h19, h₁]
    norm_num
  -- Calculate cos(3(2α - 3β))
  have h19 : cos (3 * (2 * α - 3 * β)) = -117 / 125 := by 
    have h20 : cos (3 * (2 * α - 3 * β)) = 4 * cos (2 * α - 3 * β) ^ 3 - 3 * cos (2 * α - 3 * β) := by
      rw [cos_three_mul]
    rw [h20, h17]
    norm_num
  -- Show 8α - 5β = 2(α + 2β) + 3(2α - 3β)
  have h21 : 8 * α - 5 * β = 2 * (α + 2 * β) + 3 * (2 * α - 3 * β) := by 
    linarith 
  -- Calculate sin(8α - 5β)
  rw [h21]
  have h22 : sin (2 * (α + 2 * β) + 3 * (2 * α - 3 * β)) = sin (2 * (α + 2 * β)) * cos (3 * (2 * α - 3 * β)) + cos (2 * (α + 2 * β)) * sin (3 * (2 * α - 3 * β)) := by 
    rw [sin_add]
  rw [h22, h10, h19, h12, h18]
  norm_num