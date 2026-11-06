import Mathlib

theorem algebra_300295 (a : ℝ) (x₁ x₂ : ℝ) (h₁ : x₁ ≠ x₂)
    (h₂ : x₁^2 + 6 * a * x₁ - a = 0) (h₃ : x₂^2 + 6 * a * x₂ - a = 0)
    (h₄ : a / ((1 + x₁) * (1 + x₂)) - 3 / ((1 - 6 * a - x₁) * (1 - 6 * a - x₂)) = 8 * a - 3) :
    a = 1 / 2 := by
  have h5 : x₁^2 + 6 * a * x₁ - a - (x₂^2 + 6 * a * x₂ - a) = 0 := by
    linarith [h₂, h₃]
  have h6 : (x₁ - x₂) * (x₁ + x₂ + 6 * a) = 0 := by
    ring_nf at h5 ⊢
    <;> linarith
  have h8 : x₁ + x₂ + 6 * a = 0 := by
    apply (mul_left_inj' (show x₁ - x₂ ≠ 0 by 
      intro h
      apply h₁
      linarith 
    )).mp
    linarith [h6]
  have h9 : x₁ + x₂ = -6 * a := by linarith [h8]
  have h10 : x₁ * x₂ = -a := by
    have h11 : x₁^2 + x₂^2 = 2 * a - 6 * a * (x₁ + x₂) := by
      nlinarith [h₂, h₃]
    have h12 : x₁^2 + x₂^2 = (x₁ + x₂)^2 - 2 * (x₁ * x₂) := by
      linarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂)]
    rw [h9] at h11
    rw [h12] at h11
    nlinarith
  have h11 : (1 + x₁) * (1 + x₂) = 1 - 7 * a := by
    nlinarith [h9, h10]
  have h12 : (1 - 6 * a - x₁) * (1 - 6 * a - x₂) = 1 - 7 * a := by
    nlinarith [h9, h10]
  have h13 : a / ((1 + x₁) * (1 + x₂)) - 3 / ((1 - 6 * a - x₁) * (1 - 6 * a - x₂)) =
          a / (1 - 7 * a) - 3 / (1 - 7 * a) := by
    rw [h11, h12]
  rw [h13] at h₄
  by_cases h0 : (1 - 7 * a) = 0 
  · -- Assume 1 - 7 * a = 0, so a = 1 / 7
    have ha : a = 1 / 7 := by 
      linarith 
    rw [ha] at h₄ 
    field_simp [ha, show (1 - 7 * (1 / 7 : ℝ)) = (0 : ℝ) by linarith] at h₄
    all_goals nlinarith 
  · -- Assume 1 - 7 * a ≠ 0 
    have h14 : 1 - 7 * a ≠ 0 := h0 
    have h15 : a / (1 - 7 * a) - 3 / (1 - 7 * a) = (a - 3) / (1 - 7 * a) := by 
      field_simp [h14] 
      <;> nlinarith 
    rw [h15] at h₄ 
    have h16 : (a - 3) = (8 * a - 3) * (1 - 7 * a) := by 
      field_simp [h14] at h₄ 
      linarith 
    have h17 : 56 * a^2 - 28 * a = 0  := by 
      nlinarith [h16] 
    have h18 : a * (2 * a - 1) = 0 := by 
      nlinarith [h17] 
    cases' (mul_eq_zero.1 h18) with ha1 ha2 
    · -- Assume a = 0 
      have ha0 : a = 0 := by linarith 
      have h19 : x₁ = 0 := by 
        nlinarith [h₂, ha0] 
      have h20 : x₂ = 0 := by 
        nlinarith [h₃, ha0] 
      exfalso 
      apply h₁ 
      linarith 
    · -- Assume 2 * a - 1 = 0 
      have ha1 : a = 1 / 2 := by 
        linarith 
      exact ha1