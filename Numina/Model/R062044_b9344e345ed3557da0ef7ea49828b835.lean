import Mathlib

open Real
open scoped BigOperators

theorem algebra_141320 (A B C : EuclideanSpace ℝ (Fin 3))
  (hA : A = ![3, 3, -1]) (hB : B = ![5, 1, -2]) (hC : C = ![4, 1, -3]) :
  cos (arccos (inner (B - A) (C - A) / (dist A B * dist A C))) = 8 / 9 := by 
  rw [hA, hB, hC]
  simp [dist_eq_norm, inner, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  norm_num [cos_arccos]
  all_goals norm_num [cos_arccos]