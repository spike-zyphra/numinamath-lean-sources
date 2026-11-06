import Mathlib

theorem algebra_131074 (α β : ℝ) (h₀ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₁ : β ∈ Set.Ioo 0 (Real.pi / 2))
    (h₂ : Real.sin α ^ 2 + Real.sin β ^ 2 = Real.sin (α + β)) : α + β = Real.pi / 2 := by
  rw [Set.mem_Ioo] at h₀ h₁
  have h3 : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by
    rw [Real.sin_add]
  rw [h3] at h₂
  by_cases h : α + β < Real.pi / 2
  · -- Assume that α + β < π/2
    have h4 : β < Real.pi / 2 - α := by linarith [h]
    have h5 : Real.sin β < Real.cos α := by
      have h8 : Real.sin β < Real.sin (Real.pi / 2 - α) := by
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals
          nlinarith [h₀.1, Real.pi_pos, h₀.2, h₁.1, h₁.2]
          <;> nlinarith [h4, h₀.1, Real.pi_pos, h₀.2, h₁.1, h₁.2, Real.sin_pos_of_pos_of_lt_pi h₀.1 (show α < Real.pi by linarith [h₀.2, Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi h₁.1 (show β < Real.pi by linarith [h₁.2, Real.pi_pos]), Real.sin_pi_div_two]
      have h8' : Real.sin (Real.pi / 2 - α) = Real.cos α := by
        rw [Real.sin_pi_div_two_sub]
      linarith [h8, h8']
      all_goals nlinarith
    have h10 : Real.sin α < Real.cos β := by
      have h11 : Real.sin α < Real.sin (Real.pi / 2 - β) := by
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals
          nlinarith [h₀.1, Real.pi_pos, h₀.2, h₁.1, h₁.2]
          <;> nlinarith [h4, h₀.1, Real.pi_pos, h₀.2, h₁.1, h₁.2, Real.sin_pos_of_pos_of_lt_pi h₀.1 (show α < Real.pi by linarith [h₀.2, Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi h₁.1 (show β < Real.pi by linarith [h₁.2, Real.pi_pos]), Real.sin_pi_div_two]
      have h12 : Real.sin (Real.pi / 2 - β) = Real.cos β := by
        rw [Real.sin_pi_div_two_sub]
      linarith [h12, h11]
      all_goals nlinarith
    nlinarith [Real.sin_pos_of_pos_of_lt_pi (show 0 < α by linarith [h₀.1]) (show α < Real.pi by linarith [h₀.2, Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi (show 0 < β by linarith [h₁.1]) (show β < Real.pi by linarith [h₁.2, Real.pi_pos]), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq (Real.pi / 2 - α), Real.sin_sq_add_cos_sq (Real.pi / 2 - β), Real.pi_pos, Real.sin_pi_div_two]
  · -- Assume that α + β ≥ π/2
    by_cases h' : α + β > Real.pi / 2
    · -- Assume that α + β > π/2
      have h6 : β > Real.pi / 2 - α := by linarith [h']
      have h7 : Real.sin β > Real.cos α := by
        have h8 : Real.sin β > Real.sin (Real.pi / 2 - α) := by
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals
            nlinarith [h₀.1, Real.pi_pos, h₀.2, h₁.1, h₁.2]
            <;> nlinarith [h6, h₀.1, Real.pi_pos, h₀.2, h₁.1, h₁.2, Real.sin_pos_of_pos_of_lt_pi h₀.1 (show α < Real.pi by linarith [h₀.2, Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi h₁.1 (show β < Real.pi by linarith [h₁.2, Real.pi_pos]), Real.sin_pi_div_two]
        have h8' : Real.sin (Real.pi / 2 - α) = Real.cos α := by
          rw [Real.sin_pi_div_two_sub]
        linarith [h8, h8']
        all_goals nlinarith
      have h12 : Real.sin α > Real.cos β := by
        have h11 : Real.sin α > Real.sin (Real.pi / 2 - β) := by
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals
            nlinarith [h₀.1, Real.pi_pos, h₀.2, h₁.1, h₁.2]
            <;> nlinarith [h6, h₀.1, Real.pi_pos, h₀.2, h₁.1, h₁.2, Real.sin_pos_of_pos_of_lt_pi h₀.1 (show α < Real.pi by linarith [h₀.2, Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi h₁.1 (show β < Real.pi by linarith [h₁.2, Real.pi_pos]), Real.sin_pi_div_two]
        have h13 : Real.sin (Real.pi / 2 - β) = Real.cos β := by
          rw [Real.sin_pi_div_two_sub]
        linarith [h13, h11]
        all_goals nlinarith
      nlinarith [Real.sin_pos_of_pos_of_lt_pi (show 0 < α by linarith [h₀.1]) (show α < Real.pi by linarith [h₀.2, Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi (show 0 < β by linarith [h₁.1]) (show β < Real.pi by linarith [h₁.2, Real.pi_pos]), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq (Real.pi / 2 - α), Real.sin_sq_add_cos_sq (Real.pi / 2 - β), Real.pi_pos, Real.sin_pi_div_two]
    · -- Assume that α + β = π/2
      linarith