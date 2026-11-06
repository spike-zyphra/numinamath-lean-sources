import Mathlib

theorem algebra_207734 {a b c d e f : ℝ} (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : b ≠ c)
    (h₃ : a = d) (h₄ : b = e) (h₅ : c = f) (h₆ : d ≠ e) (h₇ : d ≠ f) (h₈ : e ≠ f)
    (h₉ : a * b * c = 64) (h₁₀ : d = a + 3 * (b - a)) (h₁₁ : e = b + 3 * (c - b))
    (h₁₂ : f = c + 3 * (d - c)) :
    a = 8 / 3 := by
  have h₁₃ : d = a := by linarith [h₃]
  have h₁₄ : e = b := by linarith [h₄]
  have h₁₅ : f = c := by linarith [h₅]
  rw [h₁₃] at h₁₀
  rw [h₁₄] at h₁₁
  rw [h₁₅] at h₁₂
  have h₁₆ : a = b := by
    linarith
  exfalso
  exact h₀ h₁₆