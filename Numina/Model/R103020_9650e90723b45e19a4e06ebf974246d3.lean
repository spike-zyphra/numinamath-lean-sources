import Mathlib

open Matrix Finset

theorem algebra_13996 {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A = !![2, 1, -1; 0, 3, 1; 0, 1, 3]) :
    (A ^ 10) 1 1 = 2 ^ 9 + 2 ^ 19 := by 
  rw [hA]
  simp [pow_succ, Matrix.mul_apply, Finset.sum]
  all_goals norm_num
  <;> ring_nf
  <;> norm_num