import Mathlib

open Real
open scoped BigOperators

theorem calculus_15971 {A B C D E F P : ℝ × ℝ}
  (h₀ : A = (1, 4))
  (h₁ : B = (0, 0))
  (h₂ : C = (6, 0))
  (h₃ : D = (1 / 2) * B + (3 / 2) * C)
  (h₄ : E = (3 / 8) * A + (5 / 8) * C)
  (h₅ : P = (9 / 19) * A + (-5 / 19) * B + (15 / 19) * C) :
  P = (9 / 19) * A + (-5 / 19) * B + (15 / 19) * C := by 
  exact h₅