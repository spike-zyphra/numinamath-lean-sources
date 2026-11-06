import Mathlib

theorem calculus_22381 (D E F : ℝ × ℝ)
    (h₀ : D = (Real.sqrt 51, 7)) (h₁ : E = (0, 7)) (h₂ : F = (0, 0))
    (h₃ : Real.sin (Real.arctan (D.2 / D.1)) = 0.7) :
    Real.sqrt ((E.1 - D.1)^2 + (E.2 - D.2)^2) = Real.sqrt 51 := by
  rw [h₀] at *
  rw [h₁] at *
  simp
  <;> ring_nf <;> norm_num