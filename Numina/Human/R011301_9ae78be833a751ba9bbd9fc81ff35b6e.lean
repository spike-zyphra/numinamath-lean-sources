import Mathlib

theorem inequalities_7905 {a b c : ℝ} (h₀ : a > b ∧ b > c) (h₁ : (a - b) * (b - c) * (c - a) = -1) :
    a - c ≥ 1.5 := by 
  rcases h₀ with ⟨h01, h02⟩
  have h03 : a - c > 0 := by linarith
  have pos1 : a - b > 0 := by linarith
  have pos2 : b - c > 0 := by linarith
  have pos3 : c - a < 0 := by linarith
  have h2 : (a - c) * (a - b) * (b - c) = 1 := by
    nlinarith
  nlinarith [sq_nonneg (a - b - 1), sq_nonneg (b - c - 1), sq_nonneg (a - c - 1.5),
    mul_self_nonneg (a - b - b + c), mul_self_nonneg (a - b - (b - c) * 2 / 3),
    mul_self_nonneg (b - c - (a - c) * 2 / 3)]