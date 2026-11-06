import Mathlib

theorem number_theory_210938 (A B C D : ℝ)
    (h₀ : A = 0) (h₁ : B = 120) (h₂ : C = A + B / 2) (h₃ : D = B + A / 2) :
    C = 60 ∨ C = 120 := by
  rw [h₀, h₁] at h₂
  have hc : C = 60 := by
    linarith
  left
  exact hc