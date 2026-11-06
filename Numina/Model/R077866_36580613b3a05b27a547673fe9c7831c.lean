import Mathlib

theorem algebra_153391 (α β : ℝ) (h : α^2 - α - 2021 = 0) (h' : β^2 - β - 2021 = 0)
    (h'' : α > β) :
    ⌊α^2 - 2 * β^2 + 2 * α * β + 3 * β + 7⌋ = -6055 := by

  have h₁ : α^2 = α + 2021 := by linarith
  have h₂ : β^2 = β + 2021 := by linarith

  have h3 : α + β = 1 := by
    nlinarith [sq_pos_of_pos (show 0 < α - β by linarith), sq_nonneg (α - β), sq_nonneg (α + β - 1)]

  have h4 : α * β = -2021 := by
    nlinarith [sq_pos_of_pos (show 0 < α - β by linarith), sq_nonneg (α - β), sq_nonneg (α * β + 2021)]

  have eq1 : α^2 - 2 * β^2 + 2 * α * β + 3 * β + 7 = -6055 := by
    nlinarith [h₁, h₂, h3, h4]

  rw [eq1]
  norm_num