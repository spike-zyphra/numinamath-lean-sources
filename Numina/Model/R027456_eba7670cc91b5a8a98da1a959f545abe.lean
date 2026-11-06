import Mathlib

theorem algebra_253108 (a b c d : ℝ)
    (h₀ : a + b + c + d = 10)
    (h₁ : a * b + b * c + c * d + d * a = 25)
    (h₂ : a * b * c + b * c * d + c * d * a + d * a * b = 50) :
    a^2 + b^2 + c^2 + d^2 = 30 := by
  have h3 : (a + c) * (b + d) = 25 := by
    nlinarith
  have h4 : a + c = 5 := by
    have h5 : a + c + b + d = 10 := by linarith
    have h6 : (a + c) * (b + d) = 25 := h3
    have h7 : (a + c - 5) ^ 2 = 0 := by
      have h8 : b + d = 10 - (a + c) := by 
        linarith
      rw [h8] at h6
      nlinarith
    have h8 : a + c - 5 = 0 := by
      rw [sq_eq_zero_iff] at h7
      exact h7
    linarith
  have h5 : b + d = 5 := by
    have h9 : a + c + b + d = 10 := by linarith
    have h10 : a + c = 5 := h4
    nlinarith
  nlinarith [sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a + c - 5), sq_nonneg (b + d - 5)]