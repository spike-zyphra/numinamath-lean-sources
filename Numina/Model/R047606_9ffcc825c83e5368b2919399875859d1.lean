import Mathlib

theorem algebra_318277 (α β : ℝ) (h₀ : α ∈ Set.Ioo (3 * Real.pi / 4) Real.pi)
    (h₁ : β ∈ Set.Ioo (3 * Real.pi / 4) Real.pi) (h₂ : Real.cos (α + β) = 4 / 5)
    (h₃ : Real.sin (α - Real.pi / 4) = 12 / 13) :
    Real.cos (β + Real.pi / 4) = -56 / 65 := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  have h5 : α + β > 3 * Real.pi / 2 := by
    nlinarith [show Real.pi > 0 by linarith [Real.pi_pos]]
  have h6 : α + β < 2 * Real.pi := by
    nlinarith [show Real.pi > 0 by linarith [Real.pi_pos]]
  have h7 : Real.sin (α + β) < 0 := by
    have h8 : Real.pi < α + β := by
      nlinarith [show Real.pi > 0 by linarith [Real.pi_pos]]
    have h9 : α + β < 2 * Real.pi := by
      nlinarith [show Real.pi > 0 by linarith [Real.pi_pos]]
    have h14 : Real.sin (α + β) < 0 := by
      have h15 : Real.pi < α + β := by
        nlinarith [show Real.pi > 0 by linarith [Real.pi_pos]]
      have h16 : α + β < 2 * Real.pi := by
        nlinarith [show Real.pi > 0 by linarith [Real.pi_pos]]
      have h17 : Real.sin (α + β) = - Real.sin (2 * Real.pi - (α + β)) := by
        rw [show 2 * Real.pi - (α + β) = 2 * Real.pi - (α + β) by rfl]
        rw [Real.sin_two_pi_sub]
        <;> ring
      have h18 : Real.sin (2 * Real.pi - (α + β)) > 0 := by
        have h19 : 0 < 2 * Real.pi - (α + β) := by
          nlinarith [show Real.pi > 0 by linarith [Real.pi_pos]]
        have h20 : 2 * Real.pi - (α + β) < Real.pi := by
          nlinarith [show Real.pi > 0 by linarith [Real.pi_pos]]
        apply Real.sin_pos_of_pos_of_lt_pi
        all_goals nlinarith [show Real.pi > 0 by linarith [Real.pi_pos]]
      have h19 : Real.sin (α + β) < 0 := by
        rw [h17] at *
        linarith [h18, Real.sin_pos_of_pos_of_lt_pi (show 0 < 2 * Real.pi - (α + β) by nlinarith [show Real.pi > 0 by linarith [Real.pi_pos]]) (show 2 * Real.pi - (α + β) < Real.pi by nlinarith [show Real.pi > 0 by linarith [Real.pi_pos]])]
      linarith
    linarith
  have h8 : Real.sin (α + β) ^ 2 + Real.cos (α + β) ^ 2 = 1 := Real.sin_sq_add_cos_sq (α + β)
  rw [show Real.cos (α + β) = 4 / 5 by linarith [h₂]] at h8
  have h9 : Real.sin (α + β) = -3 / 5 := by
    nlinarith [sq_nonneg (Real.sin (α + β) + 3 / 5), h7]
  have h11 : Real.cos (β + Real.pi / 4) = Real.cos (α + β) * Real.cos (α - Real.pi / 4) + Real.sin (α + β) * Real.sin (α - Real.pi / 4) := by
    have h12 : β + Real.pi / 4 = (α + β) - (α - Real.pi / 4) := by
      ring
    rw [h12]
    rw [Real.cos_sub]
    all_goals ring
  have h13 : Real.sin (α - Real.pi / 4) = 12 / 13 := h₃
  have h14 : Real.sin (α - Real.pi / 4) ^ 2 + Real.cos (α - Real.pi / 4) ^ 2 = 1 := Real.sin_sq_add_cos_sq (α - Real.pi / 4)
  rw [show Real.sin (α - Real.pi / 4) = 12 / 13 by linarith [h₃]] at h14
  have h15 : Real.cos (α - Real.pi / 4) < 0 := by
    have h16 : α - Real.pi / 4 > Real.pi / 2 := by
      nlinarith [show Real.pi > 0 by linarith [Real.pi_pos]]
    have h17 : α - Real.pi / 4 < 3 * Real.pi / 4 := by
      nlinarith [show Real.pi > 0 by linarith [Real.pi_pos]]
    have h18 : Real.cos (α - Real.pi / 4) < 0 := by
      apply Real.cos_neg_of_pi_div_two_lt_of_lt
      all_goals
        nlinarith [show Real.pi > 0 by linarith [Real.pi_pos]]
    linarith
  have h16 : Real.cos (α - Real.pi / 4) = -5 / 13 := by
    nlinarith [sq_nonneg (Real.cos (α - Real.pi / 4) + 5 / 13), h15]
  rw [h11]
  rw [h16, h13, h9, h₂]
  all_goals linarith