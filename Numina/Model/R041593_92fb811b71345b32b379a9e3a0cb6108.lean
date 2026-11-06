import Mathlib

theorem algebra_146054 (α β : ℝ) (h₀ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₁ : β ∈ Set.Ioo 0 (Real.pi / 2))
    (h₂ : α + β = Real.pi / 2) :
    (Real.sin (Real.pi / 2 - α) + Real.cos β) / (4 * Real.sin β * 1 / Real.tan (Real.pi / 2 - α)) =
    (Real.sin β + Real.cos β) / (4 * Real.cos β) := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  have h₃ : Real.sin (Real.pi / 2 - α) = Real.sin β := by
    have h₄ : Real.pi / 2 - α = β := by
      linarith
    rw [h₄]
  have h₄ : Real.tan (Real.pi / 2 - α) = Real.tan β := by
    have h₅ : Real.pi / 2 - α = β := by
      linarith
    rw [h₅]
  have h₅ : Real.sin (Real.pi / 2 - α) + Real.cos β = Real.sin β + Real.cos β := by
    rw [h₃]
  have hdenom : 4 * Real.sin β * 1 / Real.tan (Real.pi / 2 - α) = 4 * Real.cos β := by
    rw [h₄]
    have htan : Real.tan β = Real.sin β / Real.cos β := by
      rw [Real.tan_eq_sin_div_cos]
    rw [htan]
    have h₆ : Real.sin β ≠ 0 := by
      apply ne_of_gt
      apply Real.sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_gt_31415, h₁₁, h₁₂]
      linarith [Real.pi_gt_31415, h₁₁, h₁₂]
    have h₇ : Real.cos β ≠ 0 := by
      apply ne_of_gt
      apply Real.cos_pos_of_mem_Ioo
      constructor
      linarith [Real.pi_gt_31415, h₁₁, h₁₂]
      linarith [Real.pi_gt_31415, h₁₁, h₁₂]
    field_simp [h₆, h₇]
    <;> nlinarith
  rw [h₅, hdenom]
  <;> field_simp [show Real.cos β ≠ 0 by
    apply ne_of_gt
    apply Real.cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_gt_31415, h₁₁, h₁₂]
    linarith [Real.pi_gt_31415, h₁₁, h₁₂]
  ]
  all_goals linarith