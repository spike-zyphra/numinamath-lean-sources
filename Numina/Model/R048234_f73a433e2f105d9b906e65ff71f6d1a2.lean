import Mathlib

open Real

theorem calculus_17060 (θ : ℝ) (hθ : θ = 120 * π / 180) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℝ, A = !![-1 / 2, -sqrt 3 / 2; sqrt 3 / 2, -1 / 2] := by 
  use !![-1 / 2, -sqrt 3 / 2; sqrt 3 / 2, -1 / 2]
  all_goals simp