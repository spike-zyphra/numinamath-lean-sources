import Mathlib

open Real
open scoped BigOperators

theorem algebra_129090 (A B C : EuclideanSpace ℝ (Fin 3))
  (hA : A = ![0, 2, -4])
  (hB : B = ![8, 2, 2])
  (hC : C = ![6, 2, 4]) :
  cos (arccos ((inner (B - A) (C - A)) / (norm (B - A) * norm (C - A)))) = 0.96 := by
  have h1 : (inner (B - A) (C - A)) / (norm (B - A) * norm (C - A)) = (96 / 100 : ℝ) := by 
    rw [hA, hB, hC]
    simp [Fin.sum_univ_three, inner, EuclideanSpace.norm_eq, Fin.sum_univ_succ, Fin.sum_univ_zero, sq]
    <;> norm_num
  rw [h1]
  have h2 : cos (arccos (96 / 100 : ℝ)) = (96 / 100 : ℝ) := by 
    rw [cos_arccos]
    all_goals norm_num
  rw [h2]
  all_goals norm_num