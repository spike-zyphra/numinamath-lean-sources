import Mathlib

open Matrix

theorem calculus_23377 {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A = !![3, 7; -1, -2]) :
    A^27 + A^31 + A^40 = !![-1, 0; 0, -1] := by 
  rw [hA]
  norm_num [pow_succ, Matrix.mul_fin_two]
  <;> ring_nf
  <;> norm_num