import Mathlib

theorem algebra_238498 (α β : ℝ) (h₀ : 0 < α ∧ α < Real.pi) (h₁ : Real.pi < β ∧ β < 2 * Real.pi)
    (h₂ : ∀ x : ℝ, Real.cos (x + α) + Real.sin (x + β) + Real.sqrt 2 * Real.cos x = 0) :
    α = 3 * Real.pi / 4 ∧ β = 7 * Real.pi / 4 := by

  have h3 := h₂ 0
  have h4 := h₂ (Real.pi / 2)
  have eq1 : Real.cos α + Real.sin β = -Real.sqrt 2 := by
    have h5 : Real.cos (0 + α) + Real.sin (0 + β) + Real.sqrt 2 * Real.cos (0 : ℝ) = 0 := by
      simpa using h3
    have h6 : Real.cos (0 + α) = Real.cos α := by simp
    have h7 : Real.sin (0 + β) = Real.sin β := by simp
    have h8 : Real.cos (0 : ℝ) = 1 := Real.cos_zero
    rw [h6, h7, h8] at h5
    nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2)]
  have eq2 : Real.cos β = Real.sin α := by
    have h9 : Real.cos (Real.pi / 2 + α) + Real.sin (Real.pi / 2 + β) + Real.sqrt 2 * Real.cos (Real.pi / 2 : ℝ) = 0 := by
      specialize h₂ (Real.pi / 2)
      simpa using h₂
    have h10 : Real.cos (Real.pi / 2 + α) = - Real.sin α := by
      rw [Real.cos_add]
      simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
    have h11 : Real.sin (Real.pi / 2 + β) = Real.cos β := by
      rw [Real.sin_add]
      simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
    have h12 : Real.cos (Real.pi / 2 : ℝ) = 0 := Real.cos_pi_div_two
    rw [h10, h11, h12] at h9
    nlinarith

  have h5 : Real.sin β = -Real.sqrt 2 - Real.cos α := by linarith [eq1]
  have h6 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h7 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
  rw [show Real.sin β = -Real.sqrt 2 - Real.cos α by linarith [eq1], show Real.cos β = Real.sin α by linarith [eq2]] at h7
  have h8 : Real.cos α = -Real.sqrt 2 / 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2)]
  have h9 : α = 3 * Real.pi / 4 := by
    have h10 : Real.cos α = -Real.sqrt 2 / 2 := h8
    have h11 : α > 0 := h₀.1
    have h12 : α < Real.pi := h₀.2
    have h13 : α = Real.arccos (Real.cos α) := by
      rw [Real.arccos_cos]
      all_goals linarith
    have h14 : Real.arccos (Real.cos α) = 3 * Real.pi / 4 := by
      have h15 : Real.cos α = -Real.sqrt 2 / 2 := h10
      rw [h15]
      have h16 : Real.arccos (-Real.sqrt 2 / 2) = 3 * Real.pi / 4 := by
        have h17 : Real.cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
          have h18 : 3 * Real.pi / 4 = Real.pi - (Real.pi / 4) := by ring
          rw [h18]
          rw [Real.cos_pi_sub]
          have h19 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
          linarith
        have h20 : 0 ≤ 3 * Real.pi / 4 := by linarith [Real.pi_pos]
        have h21 : 3 * Real.pi / 4 ≤ Real.pi := by linarith [Real.pi_pos]
        rw [← h17]
        apply Real.arccos_cos
        all_goals linarith
      linarith
    linarith

  have h10 : β = 7 * Real.pi / 4 := by
    have h11 : Real.cos β = Real.sin α := by linarith [eq2]
    rw [show α = 3 * Real.pi / 4 by linarith [h9]] at h11
    have h12 : Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
      have h13 : 3 * Real.pi / 4 = Real.pi - (Real.pi / 4) := by ring
      rw [h13]
      rw [Real.sin_pi_sub]
      have h14 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
      linarith
    have h13 : Real.cos β = Real.sqrt 2 / 2 := by
      linarith [h11, h12]
    have h14 : β > Real.pi := h₁.1
    have h15 : β < 2 * Real.pi := h₁.2
    have h16 : β = 7 * Real.pi / 4 := by
      have h18 : Real.cos (7 * Real.pi / 4) = Real.sqrt 2 / 2 := by
        have h19 : 7 * Real.pi / 4 = 2 * Real.pi - (Real.pi / 4) := by ring
        rw [h19]
        rw [Real.cos_two_pi_sub]
        have h20 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
        linarith
      have h19 : Real.cos β = Real.cos (7 * Real.pi / 4) := by
        linarith [h13, h18]
      have h29 : β = 7 * Real.pi / 4 := by
        have h30 : Real.cos (2 * Real.pi - β) = Real.cos (Real.pi / 4) := by
          have h31 : Real.cos (2 * Real.pi - β) = Real.cos β := by
            rw [Real.cos_two_pi_sub]
          have h32 : Real.cos (Real.pi / 4) = Real.cos (7 * Real.pi / 4) := by
            have h33 : Real.cos (7 * Real.pi / 4) = Real.cos (Real.pi / 4) := by
              have h34 : 7 * Real.pi / 4 = 2 * Real.pi - (Real.pi / 4) := by ring
              rw [h34]
              rw [Real.cos_two_pi_sub]
            linarith
          nlinarith [h13, h31, h32, h18]
        have h33 : 2 * Real.pi - β = Real.pi / 4 := by
          have h34 : Real.cos (2 * Real.pi - β) = Real.cos (Real.pi / 4) := h30
          have h35 : 0 ≤ 2 * Real.pi - β := by
            nlinarith [Real.pi_pos, h₁.2]
          have h36 : 2 * Real.pi - β ≤ Real.pi := by
            nlinarith [Real.pi_pos, h₁.1]
          have h37 : 0 ≤ Real.pi / 4 := by
            linarith [Real.pi_pos]
          have h38 : Real.pi / 4 ≤ Real.pi := by
            linarith [Real.pi_pos]
          have h39 : 2 * Real.pi - β = Real.pi / 4 := by
            apply Real.injOn_cos
            · -- Show that 2π - β ∈ [0, π]
              exact ⟨h35, h36⟩
            · -- Show that π/4 ∈ [0, π]
              exact ⟨h37, h38⟩
            · -- Show that cos(2π - β) = cos(π/4)
              exact h34
          linarith
        linarith
      linarith
    linarith
  constructor
  · exact h9
  · exact h10