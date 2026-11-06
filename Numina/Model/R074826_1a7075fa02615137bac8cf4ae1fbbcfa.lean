import Mathlib

theorem algebra_164902 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d / (v * (3 / 4)) = 3.5) (h₃ : d / v = 3.5 + 90 / v) :
    d = 600 := by
  have h4 : v * (3 / 4) ≠ 0 := by
    nlinarith
  have h5 : d = 3.5 * (v * (3 / 4)) := by
    have h6 : v * (3 / 4) ≠ 0 := by
      nlinarith
    field_simp at h₂
    nlinarith
  have h7 : d = 3.5 * v + 90 := by
    have h8 : v ≠ 0 := by linarith
    field_simp at h₃
    nlinarith
    <;> field_simp at h₃ <;> try linarith
  rw [h5] at h7
  nlinarith