import Mathlib

open BigOperators Real

theorem inequalities_101476 (A B C D : EuclideanSpace ℝ (Fin 2))
  (h : ¬Collinear ℝ {A, B, C}) (h' : ¬Collinear ℝ {A, B, D})
  (h'' : ¬Collinear ℝ {A, C, D}) (h''' : ¬Collinear ℝ {B, C, D}) :
  dist A B * dist C D + dist B C * dist A D ≥ dist A C * dist B D := by 
  apply EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist