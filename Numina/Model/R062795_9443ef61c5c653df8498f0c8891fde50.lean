import Mathlib

theorem algebra_603154 (x : Fin 5 → ℝ)
    (h₀ : 2*x 0 + x 1 + x 2 + x 3 + x 4 = 6)
    (h₁ : x 0 + 2*x 1 + x 2 + x 3 + x 4 = 12)
    (h₂ : x 0 + x 1 + 2*x 2 + x 3 + x 4 = 24)
    (h₃ : x 0 + x 1 + x 2 + 2*x 3 + x 4 = 48)
    (h₄ : x 0 + x 1 + x 2 + x 3 + 2*x 4 = 96) :
    3*x 3 + 2*x 4 = 181 := by 
  linarith