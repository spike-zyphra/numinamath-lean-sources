import Mathlib

theorem inequalities_600681 (a b c : ℝ) (h₀ : a + b > c) (h₁ : a + c > b) (h₂ : b + c > a) :
    2 / 3 * (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) ≥ a ^ 3 + b ^ 3 + c ^ 3 + a * b * c := by

  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
          mul_pos (sub_pos.mpr h₀) (sub_pos.mpr h₁), 
          mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂), 
          mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₀)]