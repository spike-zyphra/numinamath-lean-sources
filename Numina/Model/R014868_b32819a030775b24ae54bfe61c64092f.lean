import Mathlib

theorem inequalities_600889 (a b c : ℝ) (h₀ : a + b + c = 1) (h₁ : a^2 + b^2 + c^2 = 1) :
    a^5 + b^5 + c^5 ≤ 1 := by
  have h2 : a * b + a * c + b * c = 0 := by
    have eq : a * b + a * c + b * c = ( (a + b + c) ^ 2 - (a^2 + b^2 + c^2) ) / 2 := by 
      ring_nf
    rw [eq]
    rw [h₀, h₁]
    norm_num
  nlinarith [sq_nonneg (a^2 - a), sq_nonneg (b^2 - b), sq_nonneg (c^2 - c), 
          sq_nonneg (a + b + c - 1), sq_nonneg (a^2 + b^2 + c^2 - 1),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          h₀, h₁,
          sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a), 
          sq_nonneg (a + b + c), sq_nonneg (a^2 + b^2 + c^2)]