import Mathlib

theorem algebra_117067 {a b c : ℝ} (h₀ : a^2 + b^2 = 2 * c) (h₁ : 1 + a^2 = 2 * a * c) (h₂ : c^2 = a * b) :
    a = 1 ∧ b = 1 ∧ c = 1 := by
  have h3 : (a - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1)]
  have ha1 : a = 1 := by
    nlinarith
  have h4 : c = 1 := by
    rw [ha1] at h₁
    nlinarith
  have hb1 : b = 1 := by
    rw [ha1, h4] at h₂
    nlinarith
  exact ⟨ha1, hb1, h4⟩