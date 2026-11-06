import Mathlib

theorem algebra_289360 (α β : ℝ) (h₀ : α > 0) (h₁ : β > 0)
    (h₂ : α^2 - Real.sqrt 13 * α^(Real.logb 13 α) = 0) (h₃ : β^2 - Real.sqrt 13 * β^(Real.logb 13 β) = 0)
    (h₄ : α ≠ β) : α * β = 169 := by

  have h5 : α ^ 2 = Real.sqrt 13 * α ^ (Real.logb 13 α) := by
    linarith
  have h6 : β ^ 2 = Real.sqrt 13 * β ^ (Real.logb 13 β) := by
    linarith

  have h7 : Real.logb 13 (α ^ 2) = Real.logb 13 (Real.sqrt 13 * α ^ (Real.logb 13 α)) := by
    rw [h5]

  have h8 : Real.logb 13 (α ^ 2) = 2 * Real.logb 13 α := by
    simp [Real.logb_pow]

  have h9 : Real.logb 13 (Real.sqrt 13 * α ^ (Real.logb 13 α)) = Real.logb 13 (Real.sqrt 13) + Real.logb 13 (α ^ (Real.logb 13 α)) := by
    rw [Real.logb_mul (by positivity) (by positivity)]

  have h10 : Real.logb 13 (Real.sqrt 13) = (1 / 2 : ℝ) := by
    have h11 : Real.sqrt 13 = (13 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    rw [h11]
    have h12 : Real.logb 13 ((13 : ℝ) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals norm_num
    exact h12

  have h13 : Real.logb 13 (α ^ (Real.logb 13 α)) = (Real.logb 13 α) ^ 2 := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals
      try linarith
      try simp
      all_goals try linarith
    <;> try linarith

  have h5' : Real.logb 13 (β ^ 2) = Real.logb 13 (Real.sqrt 13 * β ^ (Real.logb 13 β)) := by
    rw [h6]

  have h8' : Real.logb 13 (β ^ 2) = 2 * Real.logb 13 β := by
    simp [Real.logb_pow]

  have h9' : Real.logb 13 (Real.sqrt 13 * β ^ (Real.logb 13 β)) = Real.logb 13 (Real.sqrt 13) + Real.logb 13 (β ^ (Real.logb 13 β)) := by
    rw [Real.logb_mul (by positivity) (by positivity)]

  have h13' : Real.logb 13 (β ^ (Real.logb 13 β)) = (Real.logb 13 β) ^ 2 := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals
      try linarith
      try simp
      all_goals try linarith
    <;> try linarith

  rw [h8] at h7
  rw [h9] at h7
  rw [h10] at h7
  rw [h13] at h7

  rw [h8'] at h5'
  rw [h9'] at h5'
  rw [h10] at h5'
  rw [h13'] at h5'

  have h_eq1 : (Real.logb 13 α) ^ 2 - 2 * (Real.logb 13 α) + (1 / 2 : ℝ) = 0 := by
    nlinarith

  have h_eq2 : (Real.logb 13 β) ^ 2 - 2 * (Real.logb 13 β) + (1 / 2 : ℝ) = 0 := by
    nlinarith

  have h_eq3 : Real.logb 13 α + Real.logb 13 β = 2 := by
    have h14 : (Real.logb 13 α) ^ 2 - 2 * (Real.logb 13 α) + (1 / 2 : ℝ) = 0 := h_eq1
    have h15 : (Real.logb 13 β) ^ 2 - 2 * (Real.logb 13 β) + (1 / 2 : ℝ) = 0 := h_eq2
    have h16 : (Real.logb 13 α - Real.logb 13 β) * (Real.logb 13 α + Real.logb 13 β - 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h16) with h17 h18
    · -- Case where `Real.logb 13 α - Real.logb 13 β = 0`
      exfalso
      have h18 : Real.logb 13 α = Real.logb 13 β := by linarith
      have h19 : α = β := by
        have h20 : Real.logb 13 α = Real.logb 13 β := h18
        have h21 : α = β := by
          have h22 : α = (13 : ℝ) ^ (Real.logb 13 α : ℝ) := by
            field_simp
          have h23 : β = (13 : ℝ) ^ (Real.logb 13 β : ℝ) := by
            field_simp
          rw [h22, h23, h20]
        exact h21
      contradiction
    · -- Case where `Real.logb 13 α + Real.logb 13 β - 2 = 0`
      linarith

  have h_eq4 : Real.logb 13 (α * β) = 2 := by
    have h_eq5 : Real.logb 13 (α * β) = Real.logb 13 α + Real.logb 13 β := by
      rw [Real.logb_mul (by positivity) (by positivity)]
    rw [h_eq5, h_eq3]

  have h_eq6 : α * β = (13 : ℝ) ^ (2 : ℝ) := by
    have h_eq7 : (13 : ℝ) ^ (Real.logb 13 (α * β) : ℝ) = α * β := by
      field_simp
    have h_eq8 : (13 : ℝ) ^ (Real.logb 13 (α * β) : ℝ) = (13 : ℝ) ^ (2 : ℝ) := by
      rw [h_eq4]
    linarith [h_eq7, h_eq8, h_eq4]

  rw [h_eq6]
  norm_num