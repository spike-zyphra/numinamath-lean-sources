import Mathlib

open BigOperators Real

lemma lemma_1 {u v : Fin 3 → ℝ}
    (hu : u = ![2, 2, 1]) (hv : v = ![-4, 3, 0]) :
    crossProduct u v = ![-3, -4, 14] := by
  rw [hu, hv]
  funext i
  fin_cases i <;> simp [crossProduct, Fin.sum_univ_three] <;> norm_num


theorem algebra_143762 (A B C : EuclideanSpace ℝ (Fin 3))
  (hA : A = ![2, -8, -1]) (hB : B = ![4, -6, 0]) (hC : C = ![-2, -5, -1]) :
  cos (arccos ((inner (B - A) (C - A)) / (dist A B * dist A C))) = -2 / 15 := by
  rw [hA, hB, hC]
  simp [dist_eq_norm, EuclideanSpace.norm_eq, inner, Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  ring_nf
  -- sqrt calculation
  have h1 : sqrt (9 : ℝ) = 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h2 : sqrt (25 : ℝ) = 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h1, h2]
  all_goals
    norm_num [cos_arccos]