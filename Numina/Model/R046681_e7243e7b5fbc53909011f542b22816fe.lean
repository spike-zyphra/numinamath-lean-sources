import Mathlib

theorem inequalities_605376 (a b c d : ℝ) (h₀ : 0 ≤ a) (h₁ : a ≤ b)
  (h₂ : b ≤ c) (h₃ : c ≤ d) :
  a * b^3 + b * c^3 + c * d^3 + d * a^3 ≥
  a^2 * b^2 + b^2 * c^2 + c^2 * d^2 + d^2 * a^2 := by
  have h4 : 0 ≤ b := by linarith
  have h5 : 0 ≤ c := by linarith
  have h6 : 0 ≤ d := by linarith
  have h7 : a * b ^ 3 + b * c ^ 3 + c * d ^ 3 + d * a ^ 3 - (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * d ^ 2 + d ^ 2 * a ^ 2) ≥ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), 
      sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - d),
      mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr h₁),
      mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂),
      mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₃),
      mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr h₂),
      mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr h₃),
      mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₃)
      ]
  linarith