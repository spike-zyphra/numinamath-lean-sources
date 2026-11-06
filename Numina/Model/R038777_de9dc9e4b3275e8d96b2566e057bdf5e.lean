import Mathlib

theorem algebra_12877 (θ : ℝ) (hθ : 0 < θ ∧ θ < Real.pi / 4) (h : Real.sin (2 * θ) = 0.96) :
    2020 * Real.tan θ = 2020 * (3 / 4) := by
  have h1 : 0 < θ := hθ.1
  have h2 : θ < Real.pi / 4 := hθ.2
  have h3 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := by 
    rw [Real.sin_two_mul]
  rw [h3] at h 
  have h4 : Real.sin θ * Real.cos θ = (0.48 : ℝ) := by 
    nlinarith 
  have h5 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ 
  have h6 : 0 < Real.sin θ := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [h1, Real.pi_pos]
    linarith [h1, Real.pi_pos, h2, Real.pi_pos]
  have h7 : 0 < Real.cos θ := by
    have h8 : θ < Real.pi / 2 := by
      linarith [h2, Real.pi_pos]
    have h9 : Real.cos θ > 0 := by 
      apply Real.cos_pos_of_mem_Ioo 
      constructor 
      · linarith [h8, Real.pi_pos]
      · linarith [h8, Real.pi_pos]
    linarith
  have h8 : Real.sin θ + Real.cos θ = 1.4 := by 
    have h9 : (Real.sin θ + Real.cos θ) ^ 2 = 1.96 := by
      calc 
        (Real.sin θ + Real.cos θ) ^ 2 = Real.sin θ ^ 2 + Real.cos θ ^ 2 + 2 * (Real.sin θ * Real.cos θ) := by ring 
        _ = 1 + 2 * (Real.sin θ * Real.cos θ) := by rw [h5] 
        _ = 1 + 2 * (0.48 : ℝ) := by rw [h4] 
        _ = (1.96 : ℝ) := by norm_num 
    have h10 : 0 < Real.sin θ + Real.cos θ := by 
      linarith 
    have h11 : Real.sin θ + Real.cos θ = (1.4 : ℝ) := by 
      nlinarith 
    linarith
  have h13 : Real.sin θ < Real.cos θ := by 
    have h14 : θ < Real.pi / 4 := h2 
    have h15 : Real.sin θ < Real.sin (Real.pi / 4) := by 
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals 
      linarith [h14, Real.pi_pos] 
    have h16 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four 
    have h17 : Real.cos θ > Real.cos (Real.pi / 4) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi 
      all_goals 
      linarith [h14, Real.pi_pos] 
    have h18 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four 
    have h19 : Real.sin θ < Real.cos θ := by 
      nlinarith [h15, h16, h17, h18] 
    linarith 
  have h14 : Real.sin θ - Real.cos θ = -0.2 := by 
    have h15 : (Real.sin θ - Real.cos θ) ^ 2 = (0.04 : ℝ) := by 
      calc 
        (Real.sin θ - Real.cos θ) ^ 2 = Real.sin θ ^ 2 + Real.cos θ ^ 2 - 2 * (Real.sin θ * Real.cos θ) := by ring 
        _ = 1 - 2 * (Real.sin θ * Real.cos θ) := by rw [h5] 
        _ = 1 - 2 * (0.48 : ℝ) := by rw [h4] 
        _ = (0.04 : ℝ) := by norm_num 
    have h16 : Real.sin θ - Real.cos θ < 0 := by linarith [h13] 
    have h19 : Real.sin θ - Real.cos θ = -0.2 := by 
      nlinarith 
    linarith 
  have h16 : Real.sin θ = (0.6 : ℝ) := by 
    nlinarith 
  have h17 : Real.cos θ = (0.8 : ℝ) := by 
    nlinarith 
  have h18 : Real.tan θ = (3 / 4 : ℝ) := by 
    rw [Real.tan_eq_sin_div_cos] 
    rw [h16, h17] 
    norm_num 
  linarith [h18]