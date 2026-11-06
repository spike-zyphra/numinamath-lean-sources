import Mathlib

theorem algebra_176469 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d / v = 2 + 1 / v + 3.5) (h₃ : d / (0.8 * v) = 2 + 1 / (0.8 * v) + 1.5) :
    d = 270 := by
  have h21 : d = 2 * v + 1 + 3.5 * v := by
    have h2 : v ≠ 0 := by linarith
    field_simp [h2] at h₂
    ring_nf at h₂ ⊢
    linarith
  have h31 : d = 2 * (0.8 * v) + 1 + 1.5 * (0.8 * v) := by 
    have h4 : (0.8 * v) ≠ 0 := by
      nlinarith
    field_simp [h4] at h₃
    ring_nf at h₃ ⊢
    nlinarith
  nlinarith [h21, h31, h₀, h₁]