import Mathlib

theorem algebra_98863 {a b c : ℝ} (h₁ : |a| ≥ |b + c|) (h₂ : |b| ≥ |c + a|)
    (h₃ : |c| ≥ |a + b|) : a + b + c = 0 := by
  have h1' : a^2 ≥ (b + c)^2 := by
    apply sq_le_sq.mpr
    exact h₁
  have h2' : b^2 ≥ (c + a)^2 := by
    apply sq_le_sq.mpr
    exact h₂
  have h3' : c^2 ≥ (a + b)^2 := by
    apply sq_le_sq.mpr
    exact h₃
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]