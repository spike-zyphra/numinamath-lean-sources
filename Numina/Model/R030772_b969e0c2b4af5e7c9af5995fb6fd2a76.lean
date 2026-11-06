import Mathlib

theorem algebra_241150 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d / (v + 4) + 1.5 = d / v) (h₃ : d / v + 30 / 60 = d / (2 * v) + d / (3 * v))
    (h₄ : d / v = d / (2 * v) + d / (3 * v)) :
    d = 24 := by
  have h5 : d / v = d / (2 * v) + d / (3 * v) := h₄
  have eq1 : d / v = (5 * d) / (6 * v) := by
    rw [h5]
    field_simp [h₁]
    <;> ring
  have eq2 : d = (5 * d) / 6 := by
    have hne : v ≠ 0 := by linarith
    field_simp [hne] at eq1
    nlinarith
  have eq3 : d = 0 := by
    nlinarith
  linarith