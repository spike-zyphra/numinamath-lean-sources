import Mathlib

theorem algebra_249392 (θ : ℝ) (h : Real.sin θ + Real.cos θ = 7 / 5) (ht : Real.tan θ < 1) :
    Real.sin θ = 3 / 5 := by 
  have hsin : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have h_eq1 : (Real.sin θ + Real.cos θ) ^ 2 = 49 / 25 := by
    rw [h]
    all_goals norm_num
  have h_eq2 : (Real.sin θ + Real.cos θ) ^ 2 = Real.sin θ ^ 2 + Real.cos θ ^ 2 + 2 * Real.sin θ * Real.cos θ := by ring
  have h_sin_cos_mul : Real.sin θ * Real.cos θ = 12 / 25 := by
    linarith [h_eq1, h_eq2, hsin]
  have h_eq3 : (Real.sin θ - Real.cos θ) ^ 2 = 1 / 25 := by
    have h_eq4 : (Real.sin θ - Real.cos θ) ^ 2 = Real.sin θ ^ 2 + Real.cos θ ^ 2 - 2 * (Real.sin θ * Real.cos θ) := by ring
    rw [h_eq4]
    nlinarith [hsin, h_sin_cos_mul]
  have h_sin_cos_sub : Real.sin θ - Real.cos θ = 1 / 5 ∨ Real.sin θ - Real.cos θ = -1 / 5 := by
    have h_eq5 : (Real.sin θ - Real.cos θ) ^ 2 - 1 / 25 = 0 := by linarith
    have h_eq6 : (Real.sin θ - Real.cos θ - 1 / 5) * (Real.sin θ - Real.cos θ + 1 / 5) = 0 := by
      ring_nf at h_eq5 ⊢
      nlinarith
    cases (mul_eq_zero.mp h_eq6) with
    | inl h1 =>
      left
      linarith
    | inr h2 =>
      right
      linarith
  cases h_sin_cos_sub with
  | inl h_sub =>
    have hsin1 : Real.sin θ = 4 / 5 := by 
      linarith
    have hcos1 : Real.cos θ = 3 / 5 := by 
      linarith [h, hsin1]
    have htan1 : Real.tan θ = 4 / 3 := by 
      rw [Real.tan_eq_sin_div_cos, hsin1, hcos1]
      all_goals norm_num
    linarith
  | inr h_sub =>
    have hsin2 : Real.sin θ = 3 / 5 := by 
      linarith
    have hcos2 : Real.cos θ = 4 / 5 := by 
      linarith [h, hsin2]
    have htan2 : Real.tan θ = 3 / 4 := by 
      rw [Real.tan_eq_sin_div_cos, hsin2, hcos2]
      all_goals norm_num
    linarith