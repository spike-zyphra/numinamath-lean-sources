import Mathlib

theorem algebra_266 {a b c d : ℝ} (h : 2 * a ^ 2 + 3 * c ^ 2 = 6) (h' : 2 * b ^ 2 + 3 * d ^ 2 = 6)
    (h'' : (a * d - b * c) ^ 2 = 6) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = 6 := by
  have h1 : 2 * (a ^ 2 + b ^ 2) + 3 * (c ^ 2 + d ^ 2) = 12 := by
    nlinarith
  nlinarith [sq_nonneg (a * c + b * d), sq_nonneg (a * d - b * c), 
          sq_nonneg (a ^ 2 + b ^ 2 - 3), sq_nonneg (c ^ 2 + d ^ 2 - 2), 
          sq_nonneg (a * b - c * d)]