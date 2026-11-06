import Mathlib

open Matrix

theorem algebra_176000 {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A = !![2, 5, 6; 1, 2, 5; 1, 2, 3]) :
    A⁻¹ = !![-2, -3/2, 13/2; 1, 0, -2; 0, 1/2, -1/2] := by 
  rw [hA]
  simp only [inv, Matrix.inv]
  norm_num [Matrix.det_fin_three, Matrix.mul_fin_three]
  <;> ring_nf
  <;> norm_num