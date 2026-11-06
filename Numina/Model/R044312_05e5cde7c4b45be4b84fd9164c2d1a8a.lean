import Mathlib

open Real Set

theorem inequalities_184009 (α β γ : Real) (h₀ : α ∈ Ioo 0 (π / 2)) (h₁ : β ∈ Ioo 0 (π / 2)) (h₂ : γ ∈ Ioo 0 (π / 2)) (h₃ : α + β + γ = π) :
    sin α + sin β + sin γ > 2 := by
  rcases h₀ with ⟨h01, h02⟩
  rcases h₁ with  ⟨h11, h12⟩
  rcases h₂ with  ⟨h21, h22⟩
  have h4 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [Real.pi_pos]
  have h5 : sin β > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [Real.pi_pos]
  have h6 : sin γ > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [Real.pi_pos]
  have h7 : α + β > π / 2 := by
    nlinarith [Real.pi_pos, h₃, h21, h02, h12]
  have h8 : γ = π - (α + β) := by linarith [h₃]
  have h9 : sin γ = sin (α + β) := by
    rw [h8]
    have h10 : sin (π - (α + β)) = sin (α + β) := by
      rw [sin_pi_sub]
    linarith [h10]
  have h12 : sin (α + β) = sin α * cos β + cos α * sin β := by
    rw [sin_add]
  rw [h9, h12]
  have h13 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [Real.pi_pos, h01, h02]
  have h14 : sin β > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [Real.pi_pos, h11, h12]
  have h15 : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos, h01, h02]
    · linarith [Real.pi_pos, h01, h02]
  have h16 : cos β > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos, h11, h12]
    · linarith [Real.pi_pos, h11, h12]
  have h17 : α + β > π / 2 := h7
  have h23 : sin α > cos β := by
    have h24 : α > π / 2 - β := by
      linarith [Real.pi_pos, h17, show π / 2 > 0 by linarith [Real.pi_pos]]
    have h26 : sin α > sin (π / 2 - β) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        linarith [Real.pi_pos, h01, h02, h11, h12, h24, show π / 2 - β > 0 by linarith [Real.pi_pos, h11, h12], show π / 2 - β ≤ π / 2 by linarith [Real.pi_pos, h11, h12]]
    have h27 : sin (π / 2 - β) = cos β := by
      rw [sin_pi_div_two_sub]
    nlinarith [h27, h26]
  have h29 : sin β > cos α := by
    have h24 : β > π / 2 - α := by
      linarith [Real.pi_pos, h17, show π / 2 > 0 by linarith [Real.pi_pos]]
    have h26 : sin β > sin (π / 2 - α) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        linarith [Real.pi_pos, h01, h02, h11, h12, h24, show π / 2 - α > 0 by linarith [Real.pi_pos, h01, h02], show π / 2 - α ≤ π / 2 by linarith [Real.pi_pos, h01, h02]]
    have h27 : sin (π / 2 - α) = cos α := by
      rw [sin_pi_div_two_sub]
    nlinarith [h27, h26]
  nlinarith [sq_nonneg (α - β), sq_nonneg (sin α - sin β), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, mul_pos h13 h14, mul_pos h13 h16, mul_pos h14 h15, mul_pos h15 h16, sq_nonneg (α + β - π / 2)]