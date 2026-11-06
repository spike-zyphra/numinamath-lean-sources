import Mathlib

theorem inequalities_3808 (a b c d e : ℝ) (h₀ : 0 ≤ a) (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : c ≤ d)
    (h₄ : d ≤ e) (h₅ : a + b + c + d + e = 1) :
    a * d + d * c + c * b + b * e + e * a ≤ 1 / 5 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e), 
          sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), 
          sq_nonneg (c - d), sq_nonneg (c - e), 
          sq_nonneg (d - e), 
          mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂), 
          mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₃), 
          mul_nonneg (sub_nonneg.mpr h₃) (sub_nonneg.mpr h₄), 
          mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr h₁), 
          mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr h₂), 
          mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr h₃), 
          mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr h₄)
        ]