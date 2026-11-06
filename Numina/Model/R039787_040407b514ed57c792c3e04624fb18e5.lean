import Mathlib

theorem algebra_178166 {a b c : ℝ} (h₁ : a + b + c = 5) (h₂ : a^2 + b^2 + c^2 = 15)
    (h₃ : a^3 + b^3 + c^3 = 47) :
    (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) = 625 := by
  have h₄ : a * b + b * c + c * a = 5 := by 
    have h : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by 
      ring 
    rw [h₁, h₂] at h 
    linarith 
  have h₅ : a * b * c = -1 := by 
    have h : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = (a + b + c) * ((a ^ 2 + b ^ 2 + c ^ 2) - (a * b + b * c + c * a)) := by 
      ring 
    rw [h₁, h₂, h₄, h₃] at h 
    linarith 
  have eq1 : (a ^ 2 + a * b + b ^ 2) * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) = 625 := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b + c - 5), sq_nonneg (a * b + b * c + c * a - 5),
      h₄, h₅, mul_self_nonneg (a * b), mul_self_nonneg (b * c), mul_self_nonneg (c * a)]
  exact eq1