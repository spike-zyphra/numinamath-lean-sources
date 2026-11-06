import Mathlib

open Matrix

theorem calculus_22028 {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A = !![5, -4; 0, 1]) :
    ∃ B, A * B = 1 := by

  use !![(1 / 5 : ℝ), (4 / 5 : ℝ); (0 : ℝ), (1 : ℝ)]
  rw [hA]

  simp [Matrix.mul_apply, Matrix.one_fin_two]
  all_goals norm_num
  <;> norm_num