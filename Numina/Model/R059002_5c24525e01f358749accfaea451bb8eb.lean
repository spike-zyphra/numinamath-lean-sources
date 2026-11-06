import Mathlib

theorem algebra_320617 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d / (v + 18) = 12 / 60) (h₃ : d / v = 20 / 60) :
    d = 9 := by

  have h4 : d = (1 / 3) * v := by
    have pos1 : v ≠ 0 := by linarith
    field_simp at h₃
    linarith

  have h5 : v + 18 ≠ 0 := by
    nlinarith

  have h6 : d = (1 / 5) * (v + 18) := by
    have pos1 : v + 18 ≠ 0 := h5
    field_simp at h₂
    linarith

  have h7 : (1 / 3) * v = (1 / 5) * (v + 18) := by
    linarith [h4, h6]

  have hv : v = 27 := by
    linarith

  rw [hv] at h4
  linarith