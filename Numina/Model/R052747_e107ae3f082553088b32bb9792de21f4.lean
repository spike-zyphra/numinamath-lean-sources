import Mathlib

theorem algebra_80191 (a : Fin 5 → ℝ)
    (h₀ : 2 * a 0 + a 1 + a 2 + a 3 + a 4 = 1 + (1 / 8) * a 3)
    (h₁ : 2 * a 1 + a 2 + a 3 + a 4 = 2 + (1 / 4) * a 2)
    (h₂ : 2 * a 2 + a 3 + a 4 = 4 + (1 / 2) * a 1)
    (h₃ : 2 * a 3 + a 4 = 6 + a 0) :
    a 0 + a 1 + a 2 + a 3 + a 4 = 2 := by 
  linarith