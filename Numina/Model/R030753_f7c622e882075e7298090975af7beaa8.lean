import Mathlib

theorem inequalities_301824 (a b c : ℝ) (h₀ : a + b + c = 1) (h₁ : a ^ 2 + b ^ 2 + c ^ 2 = 1) :
    a ^ 5 + b ^ 5 + c ^ 5 ≤ 1 := by
  have h2 : a * b + b * c + c * a = 0 := by
    have h_sq : a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c) ^ 2 - 2 * (a * b + b * c + c * a) := by
      ring
    rw [h₀] at h_sq
    linarith
  
  have h3 : a ^ 3 + b ^ 3 + c ^ 3 = 3 * (a * b * c) + 1 := by 
    have h3 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = (a + b + c) ^ 3 - 3 * (a + b + c) * (a * b + b * c + c * a) := by
      ring
    rw [h₀, h2] at h3
    nlinarith
  
  have h4 : a ^ 4 + b ^ 4 + c ^ 4 = 1 + 4 * (a * b * c) := by
    have h5 : a ^ 4 + b ^ 4 + c ^ 4 = (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 2 * ((a * b + b * c + c * a) ^ 2 - 2 * (a * b * c) * (a + b + c)) := by
      ring
    rw [h₀, h2] at h5
    nlinarith [h₁]

  have h5 : a ^ 5 + b ^ 5 + c ^ 5 = 1 + 5 * (a * b * c) := by
    have h6 : a ^ 5 + b ^ 5 + c ^ 5 = (a + b + c) * (a ^ 4 + b ^ 4 + c ^ 4) - (a * b + b * c + c * a) * (a ^ 3 + b ^ 3 + c ^ 3) + (a * b * c) * (a ^ 2 + b ^ 2 + c ^ 2) := by
      ring
    rw [h6, h₀, h2, h3, h4, h₁]
    nlinarith
  
  have h7 : a * b * c ≤ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      h₀, h₁, h2]

  linarith [h5, h7]