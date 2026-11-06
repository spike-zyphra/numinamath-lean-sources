import Mathlib

theorem inequalities_267024 (a b c : ℝ) (h₀ : a + b + c = 6) :
    (a * b + b * c ≤ 8) ∨ (b * c + c * a ≤ 8) ∨ (c * a + a * b ≤ 8) := by
  by_contra h
  push_neg at h
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          h₀, mul_self_nonneg (a - 2), mul_self_nonneg (b - 2), mul_self_nonneg (c - 2)]