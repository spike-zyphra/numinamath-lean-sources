import Mathlib

theorem algebra_131778 {a b : ℝ} (h₀ : a^3 + b^3 = 13) (h₁ : a^9 + b^9 = -299) : a * b = 4 := by
  have h2 : a^9 + b^9 = (a^3 + b^3)^3 - 3 * (a * b)^3 * (a^3 + b^3) := by
    ring_nf
  rw [h2] at h₁
  rw [h₀] at h₁
  have h3 : (a * b)^3 = 64 := by
    nlinarith
  have h4 : a * b = 4 := by
    have h5 : (a * b)^3 - 64 = 0 := by 
      linarith
    have h6 : (a * b - 4) * ((a * b)^2 + 4 * (a * b) + 16) = 0 := by
      nlinarith [h5]
    cases' (mul_eq_zero.mp h6) with h7 h8
    · linarith
    · 
      have h9 : (a * b)^2 + 4 * (a * b) + 16 > 0 := by
        nlinarith [sq_nonneg (a * b + 2)]
      nlinarith
  exact h4