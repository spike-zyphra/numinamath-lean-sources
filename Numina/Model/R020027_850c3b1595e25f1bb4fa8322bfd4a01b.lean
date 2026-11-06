import Mathlib

theorem algebra_241505 (a b c d e : ℝ)
    (h₀ : a = 60) (h₁ : e = 300)
    (h₂ : a * b * c = 810000) (h₃ : b * c * d = 2430000) (h₄ : c * d * e = 8100000) :
    c = 150 := by
  rw [h₀] at h₂
  rw [h₁] at h₄
  have eq1 : b * c = 13500 := by
    nlinarith
  have eq2 : c * d = 27000 := by
    nlinarith
  have eq3 : d = 180 := by
    have h5 : (b * c) * d = 2430000 := by linarith
    rw [show b * c = 13500 by linarith] at h5
    nlinarith
  have h6 : d = 180 := eq3
  have eq4 : c = 150 := by
    rw [h6] at eq2
    nlinarith
  exact eq4