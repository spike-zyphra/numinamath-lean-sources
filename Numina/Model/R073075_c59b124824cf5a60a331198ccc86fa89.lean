import Mathlib

open Matrix

theorem calculus_12237 {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A = !![0, 0, 1; 1, 0, 0; 0, 1, 0]) : A ^ 100 = A := by 
  rw [hA]
  norm_num [pow_succ, Matrix.mul_fin_three]
  <;> ring_nf <;> simp [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] <;> ring