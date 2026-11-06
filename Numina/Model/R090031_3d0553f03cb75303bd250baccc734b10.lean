import Mathlib

theorem calculus_16082 {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A = !![4, 1; -9, -2]) : A ^ 100 = !![301, 100; -900, -299] := by 
  rw [hA]
  -- Compute A^100
  norm_num [pow_succ, Matrix.mul_fin_two]
  <;> ring_nf
  <;> norm_num