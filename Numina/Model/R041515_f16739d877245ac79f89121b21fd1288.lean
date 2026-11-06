import Mathlib

open Real Set
open scoped Real

theorem algebra_10400 (α β : ℝ) (h₁ : α ∈ Ioo (3 * π / 4) π)
    (h₂ : β ∈ Ioo (3 * π / 4) π) (h₃ : sin (α + β) = -3 / 5)
    (h₄ : sin (β - π / 4) = 12 / 13) :
    cos (α + π / 4) = -56 / 65 := by
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  rcases h₂ with ⟨h₂₁, h₂₂⟩
  have h5 : cos (α + β) = 4 / 5 := by
    have h5' : cos (α + β) ^ 2 + sin (α + β) ^ 2 = 1 := Real.cos_sq_add_sin_sq (α + β)
    rw [h₃] at h5'
    have h7 : cos (α + β) > 0 := by
      have h8 : α + β > π := by
        nlinarith [Real.pi_pos]
      have h9 : α + β < 2 * π := by
        nlinarith [Real.pi_pos]
      have h13 : α + β - 2 * π > -π := by
        nlinarith [Real.pi_pos]
      have h14 : α + β - 2 * π < 0 := by
        nlinarith [Real.pi_pos]
      have h15 : cos (α + β) = cos ((α + β - 2 * π) + 2 * π) := by
        ring_nf
      rw [h15]
      have h16 : -π < α + β - 2 * π := by
        nlinarith [Real.pi_pos]
      have h17 : α + β - 2 * π < 0 := by
        nlinarith [Real.pi_pos]
      have h18 : cos ( (α + β - 2 * π) ) > 0 := by
        have h19 : (α + β - 2 * π) > -(Real.pi / 2) := by
          nlinarith [Real.pi_pos]
        have h20 : (α + β - 2 * π) < Real.pi / 2 := by
          nlinarith [Real.pi_pos]
        apply cos_pos_of_mem_Ioo
        constructor
        · nlinarith
        · nlinarith
      rw [cos_add_two_pi]
      exact h18
    nlinarith
  have h8 : β - π / 4 > Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have h9 : β - π / 4 < Real.pi := by
    nlinarith [Real.pi_pos]
  have h10 : cos (β - π / 4) < 0 := by
    apply cos_neg_of_pi_div_two_lt_of_lt
    all_goals linarith [Real.pi_pos]
  have h55 : cos (β - π / 4) = -5 / 13 := by
    have h101 : cos (β - π / 4) < 0 := h10
    have h7' : cos (β - π / 4) ^ 2 + sin (β - π / 4) ^ 2 = 1 := Real.cos_sq_add_sin_sq (β - π / 4)
    rw [h₄] at h7'
    have h102 : cos (β - π / 4) < 0 := h10
    nlinarith
  have h34 : α + π / 4 = (α + β) - (β - π / 4) := by
    ring_nf
  rw [h34]
  have h45 : cos ((α + β) - (β - π / 4)) = cos (α + β) * cos (β - π / 4) + sin (α + β) * sin (β - π / 4) := by
    rw [cos_sub]
  rw [h45]
  rw [h5, h55, h₃, h₄]
  all_goals nlinarith