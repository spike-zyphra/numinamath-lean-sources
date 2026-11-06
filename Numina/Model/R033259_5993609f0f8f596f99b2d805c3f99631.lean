import Mathlib

theorem algebra_101964 (a b : ℝ) (h₀ : a = b - 1) (h₁ : 1 ≤ b ∧ b ≤ 3) :
    Real.sqrt (a^2 + b^2 - 2 * b + 1) +
    Real.sqrt (a^2 + b^2 - 4 * a - 6 * b + 13) = 2 * Real.sqrt 2 := by
  have h2 : 1 ≤ b := h₁.1
  have h3 : b ≤ 3 := h₁.2
  have ha : a = b - 1 := h₀
  have h4 : a ^ 2 + b ^ 2 - 2 * b + 1 = 2 * (b - 1) ^ 2 := by
    rw [ha]
    nlinarith
  have h5 : a ^ 2 + b ^ 2 - 4 * a - 6 * b + 13 = 2 * (b - 3) ^ 2 := by 
    rw [ha]
    nlinarith
  have h6 : Real.sqrt (a^2 + b^2 - 2 * b + 1) = Real.sqrt (2 * (b - 1) ^ 2) := by 
    rw [h4]
  have h7 : Real.sqrt (a^2 + b^2 - 4 * a - 6 * b + 13) = Real.sqrt (2 * (b - 3) ^ 2) := by 
    rw [h5]
  have h8 : Real.sqrt (2 * (b - 1) ^ 2) = Real.sqrt 2 * |b - 1| := by
    have h9 : Real.sqrt (2 * (b - 1) ^ 2) = Real.sqrt (2) * Real.sqrt ((b - 1) ^ 2) := by
      rw [Real.sqrt_mul (by linarith)]
    have h10 : Real.sqrt ((b - 1) ^ 2) = |b - 1| := by 
      rw [Real.sqrt_sq_eq_abs]
    rw [h9, h10]
  have h9 : Real.sqrt (2 * (b - 3) ^ 2) = Real.sqrt 2 * |b - 3| := by 
    have h10 : Real.sqrt (2 * (b - 3) ^ 2) = Real.sqrt (2) * Real.sqrt ((b - 3) ^ 2) := by 
      rw [Real.sqrt_mul (by linarith)]
    have h11 : Real.sqrt ((b - 3) ^ 2) = |b - 3| := by 
      rw [Real.sqrt_sq_eq_abs]
    rw [h10, h11]
  rw [h6, h8]
  rw [h7, h9]
  have h10 : 0 ≤ b - 1 := by 
    nlinarith
  have h11 : |b - 1| = b - 1 := by 
    rw [abs_of_nonneg h10]
  have h12 : b - 3 ≤ 0 := by 
    nlinarith
  have h13 : |b - 3| = 3 - b := by 
    rw [abs_of_nonpos h12]
    all_goals linarith
  rw [h11, h13]
  have h14 : Real.sqrt 2 * (b - 1) + Real.sqrt 2 * (3 - b) = 2 * Real.sqrt 2 := by
    have h15 : Real.sqrt 2 * (b - 1) + Real.sqrt 2 * (3 - b) = Real.sqrt 2 * ((b - 1) + (3 - b)) := by 
      ring
    have h16 : (b - 1 : ℝ) + (3 - b : ℝ) = 2 := by 
      linarith
    rw [h15, h16]
    all_goals ring
  linarith [h14]