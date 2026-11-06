import Mathlib

theorem algebra_109340 (α β : ℝ) (h₁ : 3 * Real.pi / 4 < α ∧ α < Real.pi)
    (h₂ : 3 * Real.pi / 4 < β ∧ β < Real.pi) (h₃ : Real.cos (α + β) = 4 / 5)
    (h₄ : Real.sin (α - Real.pi / 4) = 12 / 13) :
    Real.cos (β + Real.pi / 4) = -56 / 65 := by 
  have h1 : 3 * Real.pi / 4 < α := h₁.1 
  have h2 : α < Real.pi := h₁.2 
  have h3' : 3 * Real.pi / 4 < β := h₂.1 
  have h4' : β < Real.pi := h₂.2 

  have h5 : Real.sin (α + β) < 0 := by
    have h1 : Real.pi < (α + β) := by 
      nlinarith 
    have h2 : α + β < 2 * Real.pi := by 
      nlinarith 
    have h4 : Real.sin (α + β) < 0 := by
      have h1 : Real.pi < α + β := by
        linarith 
      have h2 : α + β < 2 * Real.pi := by
        linarith 
      have h5 : Real.sin (α + β) = Real.sin (α + β - 2 * Real.pi + 2 * Real.pi) := by ring 
      rw [h5] 
      have h6 : Real.sin (α + β - 2 * Real.pi + 2 * Real.pi) = Real.sin (α + β - 2 * Real.pi) := by 
        rw [Real.sin_add, Real.sin_two_pi, Real.cos_two_pi]
        all_goals ring_nf
      rw [h6]
      have h7 : -Real.pi < α + β - 2 * Real.pi := by 
        nlinarith 
      have h8 : α + β - 2 * Real.pi < 0 := by 
        nlinarith 
      have h9 : Real.sin (α + β - 2 * Real.pi) < 0 := by 
        apply Real.sin_neg_of_neg_of_neg_pi_lt 
        all_goals 
          nlinarith 
      linarith 
    linarith

  have h6 : Real.sin (α + β) = -3 / 5 := by
    have h5 : Real.sin (α + β) < 0 := h5
    have hsin2 : Real.sin (α + β) ^ 2 + Real.cos (α + β) ^ 2 = 1 := Real.sin_sq_add_cos_sq (α + β)
    rw [h₃] at hsin2
    have hsin2' : Real.sin (α + β) ^ 2 = 9 / 25 := by 
      nlinarith 
    have hsin : Real.sin (α + β) < 0 := h5
    have h7 : Real.sin (α + β) = -3 / 5 := by
      nlinarith 
    exact h7

  have h7 : Real.pi / 2 < α - Real.pi / 4 := by 
    nlinarith 
  have h8 : α - Real.pi / 4 < 3 * Real.pi / 4 := by 
    nlinarith 
  have h9 : Real.cos (α - Real.pi / 4) < 0 := by 
    apply Real.cos_neg_of_pi_div_two_lt_of_lt 
    all_goals 
      linarith [Real.pi_pos] 
  have h10 : Real.cos (α - Real.pi / 4) = -5 / 13 := by
    have h9 : Real.cos (α - Real.pi / 4) < 0 := h9
    have hcos2 : Real.sin (α - Real.pi / 4) ^ 2 + Real.cos (α - Real.pi / 4) ^ 2 = 1 := Real.sin_sq_add_cos_sq (α - Real.pi / 4)
    rw [h₄] at hcos2 
    have hcos2' : Real.cos (α - Real.pi / 4) ^ 2 = 25 / 169 := by 
      nlinarith 
    have hcos2'' : Real.cos (α - Real.pi / 4) < 0 := h9 
    nlinarith

  have h8 : β + Real.pi / 4 = (α + β) - (α - Real.pi / 4) := by
    ring_nf 
  rw [h8]
  have hcos : Real.cos ((α + β) - (α - Real.pi / 4)) =
          Real.cos (α + β) * Real.cos (α - Real.pi / 4) + Real.sin (α + β) * Real.sin (α - Real.pi / 4) := by 
    rw [Real.cos_sub]
  rw [hcos]
  rw [h₃, h6, h₄, h10]
  norm_num