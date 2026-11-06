import Mathlib

theorem inequalities_599650 (x y z t : ℝ) (h₀ : x + y + z + t = 0) (h₁ : x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2 = 1) :
    -1 ≤ x * y + y * z + z * t + t * x ∧ x * y + y * z + z * t + t * x ≤ 0 := by
  constructor
  · -- Prove that -1 ≤ x * y + y * z + z * t + t * x
    nlinarith [sq_nonneg (x + z - (y + t)), sq_nonneg (x - z), sq_nonneg (y - t), 
      sq_nonneg (x + y - z - t), sq_nonneg (x + t - (y + z)), 
      h₀, h₁, mul_self_nonneg (x + z + y + t)]
  · -- Prove that x * y + y * z + z * t + t * x ≤ 0
    nlinarith [sq_nonneg (x + z - (y + t)), sq_nonneg (x - z), sq_nonneg (y - t), 
      sq_nonneg (x + y - z - t), sq_nonneg (x + t - (y + z)), 
      h₀, h₁, mul_self_nonneg (x + z + y + t)]