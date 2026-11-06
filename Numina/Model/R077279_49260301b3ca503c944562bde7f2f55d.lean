import Mathlib

open Matrix

theorem calculus_23403 (v : ℝ × ℝ) (h : v = (-1, 3)) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℝ, A = !![-4 / 5, -3 / 5; -3 / 5, 4 / 5] := by 
  use !![-4 / 5, -3 / 5; -3 / 5, 4 / 5]
  all_goals simp