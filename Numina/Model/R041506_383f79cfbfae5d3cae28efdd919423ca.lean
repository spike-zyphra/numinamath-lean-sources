import Mathlib

open Matrix Real

theorem calculus_23066 {A B : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A⁻¹ = !![4, 0; 1, -1]) (hB : B⁻¹ = !![2, -1; -1, 3]) :
    (A * B)⁻¹ = !![7, 1; -1, -3] := by
  have h1 : (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
    rw [Matrix.mul_inv_rev]
  rw [h1, hA, hB]
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  all_goals norm_num