import Mathlib

open Matrix

theorem calculus_14738 {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A = !![2, 3; -1, 7]) :
    A⁻¹ = !![7/17, -3/17; 1/17, 2/17] := by 
  rw [hA]
  simp only [inv, Matrix.inv]
  norm_num
  <;> ring_nf
  <;> norm_num