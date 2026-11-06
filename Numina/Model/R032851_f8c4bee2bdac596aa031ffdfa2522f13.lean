import Mathlib

open Real Set
open scoped Real

theorem algebra_240006 (α β : ℝ) (h₁ : α ∈ Ioo (3 * π / 4) π)
  (h₂ : β ∈ Ioo (3 * π / 4) π) (h₃ : cos (α + β) = 4 / 5) (h₄ : sin (α - π / 4) = 12 / 13) :
  cos (β + π / 4) = -56 / 65 := by
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  rcases h₂ with ⟨h₂₁, h₂₂⟩
  have h5 : α + β > 3 * π / 2 := by
    nlinarith [h₁₁, h₂₁, Real.pi_pos]
  have h6 : α + β < 2 * π := by
    nlinarith [h₁₂, h₂₂, Real.pi_pos]
  have h8 : sin (α + β) < 0 := by
    have h14 : π < α + β := by
      nlinarith [h5, Real.pi_pos]
    have h15 : α + β < 2 * π := h6
    have h16 : α + β - π > 0 := by
      linarith [Real.pi_pos, h14]
    have h18 : α + β - π < π := by
      linarith [Real.pi_pos, h15]
    have h19 : sin (α + β) = -sin (α + β - π) := by
      rw [show α + β = (α + β - π) + π by linarith]
      rw [sin_add]
      simp [sin_pi, cos_pi]
      all_goals linarith
    have h23 : sin (α + β - π) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      · -- Show that 0 < α + β - π
        linarith [Real.pi_pos]
      · -- Show that α + β - π < π
        linarith [Real.pi_pos]
    linarith [h19, h23]
  have h24 : sin (α + β) = -3 / 5 := by
    have h24 : sin (α + β) ^ 2 + cos (α + β) ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq (α + β)
    rw [h₃] at h24
    nlinarith [h8]
  have h5' : α - π / 4 > π / 2 := by
    nlinarith [h₁₁, Real.pi_pos]
  have h6' : α - π / 4 < 3 * π / 4 := by
    nlinarith [h₁₂, Real.pi_pos]
  have h11 : cos (α - π / 4) < 0 := by
    have h9 : π / 2 < α - π / 4 := h5'
    have h10 : α - π / 4 < 3 * π / 4 := h6'
    have h11 : cos (α - π / 4) < 0 := by
      apply cos_neg_of_pi_div_two_lt_of_lt
      all_goals linarith [Real.pi_pos]
    assumption
  have h15 : cos (α - π / 4) = -5 / 13 := by
    have h12' : cos (α - π / 4) ^ 2 + sin (α - π / 4) ^ 2 = 1 := by
      apply Real.cos_sq_add_sin_sq
    rw [h₄] at h12'
    have h11' : cos (α - π / 4) < 0 := h11
    nlinarith
  have h18 : β + π / 4 = (α + β) - (α - π / 4) := by
    linarith [show α = α by rfl, show β = β by rfl]
  rw [h18]
  rw [cos_sub]
  rw [h₃, h15, h24, h₄]
  norm_num
  <;> linarith [Real.pi_pos]