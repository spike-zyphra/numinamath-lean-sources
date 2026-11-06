import Mathlib

theorem algebra_199823 (a b c d e f : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : d = a + 1 ∧ e = b + 1 ∧ f = c + 1)
    (h₂ : d * e * f = a * b * c + 18)
    (h₃ : 2 * (d * e + e * f + f * d) = 2 * (a * b + b * c + c * a) + 30) :
    2 * (a * b + b * c + c * a) = 22 := by
  rcases h₀ with ⟨ha, hb, hc⟩
  rcases h₁ with ⟨hd, he, hf⟩
  rw [hd] at h₂ h₃
  rw [he] at h₂ h₃
  rw [hf] at h₂ h₃
  ring_nf at h₂ h₃
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]