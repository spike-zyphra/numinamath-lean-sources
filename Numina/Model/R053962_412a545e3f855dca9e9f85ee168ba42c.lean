import Mathlib

open Matrix

theorem calculus_23409 : ∃ M : Matrix (Fin 2) (Fin 2) ℝ, ∀ a b c d : ℝ,
    M * !![a, b; c, d] = !![c, d; a, b] := by
  use !![0, 1; 1, 0]
  intro a b c d
  simp [Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add, mul_comm]
  <;> ring