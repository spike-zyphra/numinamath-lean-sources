import Mathlib

open Real
open scoped BigOperators

theorem inequalities_106681
  (A B C D : EuclideanSpace ℝ (Fin 2))
  (h : A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D) :
  dist A C * dist B D ≤ dist A B * dist C D + dist B C * dist A D := by 
  apply EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist