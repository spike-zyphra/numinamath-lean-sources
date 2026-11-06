import Mathlib

theorem inequalities_77986 (p q : ℝ) (h₀ : 0 < p) (h₁ : 0 < q)
    (h₂ : p + q < 1) (x y : ℝ) :
    (p * x + q * y) ^ 2 ≤ p * x ^ 2 + q * y ^ 2 := by
  have hp : p > 0 := h₀
  have hq : q > 0 := h₁
  have hp1 : p < 1 := by linarith
  have hq1 : q < 1 := by linarith
  have hp2 : 0 < 1 - p := by linarith
  have hq2 : 0 < 1 - q := by linarith

  have h4 : p * x ^ 2 + q * y ^ 2 - (p * x + q * y) ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg (x * p - y * q), sq_nonneg (x - y), sq_nonneg (x * (1 - p) - y * (1 - q)), sq_nonneg (x * (1 - q) - y * (1 - p)), 
      mul_pos hp hq, mul_pos hp hp2, mul_pos hq hq2, mul_pos hp2 hq2]

  linarith