import Mathlib

theorem algebra_5061 {α β : ℝ} (h : α^2 - 11*α + 29 = 0 ∧ β^2 - 11*β + 29 = 0)
    (h₁ : α ≠ β) : α*β^2 + α^2*β = 319 := by 
  have h2 : α^2 - 11 * α + 29 = 0 := h.1
  have h3 : β^2 - 11 * β + 29 = 0 := h.2
  have eq1 : α + β = 11 := by
    have h4 : α^2 - β^2 = 11 * (α - β) := by
      linarith [h2, h3]
    have h5 : α^2 - β^2 = (α - β) * (α + β) := by
      ring
    rw [h5] at h4
    have h6 : (α - β) * (α + β - 11) = 0 := by
      linarith
    have h7 : α - β ≠ 0 := sub_ne_zero.mpr h₁
    have h8 : α + β - 11 = 0 := by
      apply_fun (λ x => x / (α - β)) at h6
      field_simp [h7] at h6
      linarith
    linarith
  have eq2 : α * β = 29 := by
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr h₁), eq1]
  have eq3 : α * β^2 + α^2 * β = (α * β) * (α + β) := by
    ring
  rw [eq3, eq2, eq1]
  all_goals norm_num