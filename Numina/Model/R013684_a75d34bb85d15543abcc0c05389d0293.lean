import Mathlib

theorem algebra_10658 (α β : ℝ) (h₀ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₁ : β ∈ Set.Ioo (-Real.pi / 2) 0)
    (h₂ : Real.sin β = -5 / 13) (h₃ : Real.sqrt ((Real.cos α - Real.cos β) ^ 2 + (Real.sin α - Real.sin β) ^ 2) = 2 * Real.sqrt 5 / 5) :
    Real.sin α = 33 / 65 := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with  ⟨h₁₁, h₁₂⟩
  have h₄ : Real.cos β = 12 / 13 := by
    have h₄ : Real.sin β = -5 / 13 := h₂
    have h₅ : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
    rw [h₂] at h₅
    have h₆ : Real.cos β ^ 2 = 144 / 169 := by
      nlinarith
    have h₇ : Real.cos β > 0 := by
      have h₈ : β > -Real.pi / 2 := h₁₁
      have h₉ : β < 0 := h₁₂
      have h₁₀ : Real.cos β > 0 := by
        apply Real.cos_pos_of_mem_Ioo
        constructor
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
      exact h₁₀
    have h₁₂ : Real.cos β = 12 / 13 := by
      nlinarith
    exact h₁₂

  have h₅ : (Real.cos α - Real.cos β) ^ 2 + (Real.sin α - Real.sin β) ^ 2 = 4 / 5 := by
    calc
      (Real.cos α - Real.cos β) ^ 2 + (Real.sin α - Real.sin β) ^ 2 = (Real.sqrt ((Real.cos α - Real.cos β) ^ 2 + (Real.sin α - Real.sin β) ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = (2 * Real.sqrt 5 / 5) ^ 2 := by rw [h₃]
      _ = 4 * (Real.sqrt 5 ^ 2) / 25 := by ring
      _ = 4 * (5) / 25 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      _ = 4 / 5 := by norm_num

  rw [show Real.sin β = -5 / 13 by linarith [h₂], show Real.cos β = 12 / 13 by linarith [h₄]] at h₅

  have h₆ : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h₇ : Real.sin α > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [h₀₁, Real.pi_pos]
    · linarith [h₀₂, Real.pi_pos]
  have h₈ : Real.cos α > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [h₀₁, Real.pi_pos]
    · linarith [h₀₂, Real.pi_pos]
  nlinarith [h₅, h₆, h₇, h₈]