import Mathlib

open Real 

theorem Algebra_611308 {x y: ℝ} (h1 : x ^ 2 = x + y + 4) (h2 : y ^ 2 = y - 15 * x + 36) : 
x = 2 ∨ x = - 1 + 5 ^ (1 / (2 : ℝ)) ∨ x = - 1 - 5 ^ (1 / (2 : ℝ)) := by
  have h3 : y = x^2 - x - 4 := by 
    nlinarith
  rw [h3] at h2
  have h4 : (x - 2)^2 * (x^2 + 2 * x - 4) = 0 := by 
    nlinarith [sq_nonneg (x^2 - x - 4 - (x^2 - 16 * x + 32)), sq_nonneg (x - 2), sq_nonneg (x + 1), sq_nonneg (y - (x^2 - x - 4))]
  cases (mul_eq_zero.1 h4) with
  | inl h5 =>
    have : x - 2 = 0 := by 
      apply pow_eq_zero 
      exact h5
    have hx : x = 2 := by linarith
    left 
    exact hx
  | inr h6 =>
    have h7 : x^2 + 2 * x - 4 = 0 := by
      linarith [h6]
    have h8 : (x + 1)^2 = 5 := by 
      nlinarith 
    have h9 : (x + 1) = Real.sqrt 5 ∨ (x + 1) = - (Real.sqrt 5) := by 
      have h55 : (x + 1) ^ 2 = 5 := h8
      have : (x + 1) ^ 2 - (5 : ℝ) = 0 := by linarith 
      have : ((x + 1) - Real.sqrt 5) * ((x + 1) + Real.sqrt 5) = 0 := by 
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
      cases (mul_eq_zero.1 this) with
      | inl h => 
        left 
        linarith 
      | inr h => 
        right 
        nlinarith 
    cases h9 with
    | inl h10 =>
      have h11 : x = -1 + Real.sqrt 5 := by
        linarith 
      rw [h11]
      have h12 : Real.sqrt 5 = (5 : ℝ) ^ (1 / 2 : ℝ) := by 
        rw [Real.sqrt_eq_rpow]
      rw [h12]
      all_goals norm_num
    | inr h11 =>
      have h12 : x = -1 - Real.sqrt 5 := by
        linarith 
      rw [h12]
      have h13 : Real.sqrt 5 = (5 : ℝ) ^ (1 / 2 : ℝ) := by 
        rw [Real.sqrt_eq_rpow]
      rw [h13]
      all_goals norm_num