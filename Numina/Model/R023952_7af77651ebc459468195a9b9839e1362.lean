import Mathlib


theorem algebra_186249 (α β : ℝ) (h₀ : Real.tan (α + β) = 9 / 19) (h₁ : Real.tan α = -4)
    (h₂ : Real.pi / 2 < β ∧ β < Real.pi) :
    β = Real.pi - Real.arctan 5 := by

  have h₃ : Real.cos (α + β) ≠ 0 := by
    by_contra h
    have h₄ : Real.tan (α + β) = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h]
    rw [h₄] at h₀
    norm_num at h₀

  have h₄ : Real.cos α ≠ 0 := by
    by_contra h
    have h₅ : Real.tan α = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h]
    rw [h₅] at h₁
    norm_num at h₁

  have h₅ : Real.sin α = -4 * Real.cos α := by
    have h₆ : Real.cos α ≠ 0 := h₄
    have h₇ : Real.tan α = Real.sin α / Real.cos α := by
      rw [Real.tan_eq_sin_div_cos]
    rw [h₇] at h₁
    field_simp [h₄] at h₁ ⊢
    linarith

  have h₆ : Real.sin (α + β) / Real.cos (α + β) = 9 / 19 := by
    have h₇ : Real.tan (α + β) = Real.sin (α + β) / Real.cos (α + β) := by
      rw [Real.tan_eq_sin_div_cos]
    rw [h₇] at h₀
    all_goals
      linarith

  have h₇ : Real.sin (α + β) = 9 / 19 * Real.cos (α + β) := by
    have h₈ : Real.cos (α + β) ≠ 0 := h₃
    field_simp at h₆ ⊢
    linarith

  have h₈ : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by
    rw [Real.sin_add]

  have h₉ : Real.cos (α + β) = Real.cos α * Real.cos β - Real.sin α * Real.sin β := by
    rw [Real.cos_add]

  rw [h₈, h₉] at h₇
  rw [show Real.sin α = -4 * Real.cos α by linarith [h₅]] at h₇

  have h₁₃ : Real.sin β = -5 * Real.cos β := by
    have h₃₂ : Real.cos α ≠ 0 := h₄
    apply (mul_left_inj' (show Real.cos α ≠ 0 by exact h₃₂)).mp
    linarith

  have h₆₆ : Real.tan β = -5 := by
    rw [Real.tan_eq_sin_div_cos]
    have h₅₆ : Real.cos β ≠ 0 := by 
      by_contra h
      rw [h] at h₁₃
      have : Real.sin β = 0 := by linarith
      have h₂₃ : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
      rw [this, h] at h₂₃
      norm_num at h₂₃
    field_simp [h₅₆]
    linarith [h₁₃]

  have h₆₇ : β = Real.pi - Real.arctan 5 := by
    have h₃₆ : Real.tan (Real.pi - β) = 5 := by
      have h₃₇ : Real.tan (Real.pi - β) = - Real.tan β := by
        rw [Real.tan_pi_sub]
      rw [h₃₇, h₆₆]
      all_goals norm_num

    have h₃₈ : Real.pi - β > 0 := by
      nlinarith [Real.pi_pos, h₂.1, h₂.2]

    have h₃₉ : Real.pi - β < Real.pi / 2 := by
      nlinarith [Real.pi_pos, h₂.1, h₂.2]

    have h₄₂ : Real.pi - β = Real.arctan 5 := by
      have h₄₁ : Real.arctan (Real.tan (Real.pi - β)) = Real.arctan 5 := by
        rw [h₃₆]
      have h₄₀ : Real.arctan (Real.tan (Real.pi - β)) = Real.pi - β := by
        apply Real.arctan_tan
        all_goals
          nlinarith [Real.pi_pos, h₂.1, h₂.2]
      linarith [h₄₁, h₄₀]

    linarith

  exact h₆₇