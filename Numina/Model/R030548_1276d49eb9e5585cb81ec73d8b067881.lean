import Mathlib

open Real
open scoped BigOperators

theorem inequalities_264668
  (A B C D : EuclideanSpace ℝ (Fin 2))
  : dist A B * dist C D + dist B C * dist A D ≥ dist A C * dist B D := by
    apply EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist