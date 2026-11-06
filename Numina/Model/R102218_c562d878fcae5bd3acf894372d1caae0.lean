import Mathlib

theorem algebra_240737 (d m1 m2 : ℝ) (h₀ : d > 0) (h₁ : m1 > 0) (h₂ : m2 > 0)
    (h₃ : m1 = (1 - 10 / 100) * m2) (h₄ : m1 * (1 + 10 / 100) = d) :
    d / m2 < d / m1 := by
  have h₁₀ : m1 = (9 / 10) * m2 := by
    linarith
  have h₁₁ : d = m1 * (11 / 10) := by
    linarith
  have h₁₂ : m1 < m2 := by
    nlinarith
  have h₁₃ : d > 0 := h₀
  have h₁₄ : m1 > 0 := h₁
  have h₁₅ : m2 > 0 := h₂
  have h₁₇ : d = m1 * (11 / 10) := by linarith
  have h₁₈ : m1 = (9 / 10) * m2 := by linarith
  have h₁₉ : d / m2 = (99 / 100 : ℝ) := by
    rw [h₁₇, h₁₈]
    field_simp at *
    <;> nlinarith
    all_goals linarith
  have h₁₁₀ : d / m1 = (11 / 10 : ℝ) := by
    rw [h₁₇]
    field_simp at *
    <;> nlinarith
    all_goals linarith
  linarith [h₁₉, h₁₁₀]