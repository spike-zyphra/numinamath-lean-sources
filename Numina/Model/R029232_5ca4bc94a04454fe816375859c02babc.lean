import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_186044 (u : ℝ → ℝ → ℝ → ℝ)
  (hu : u = λ x y z => x * y + y * z + 1)
  (A B : EuclideanSpace ℝ (Fin 3))
  (hA : A = ![0, -2, -1])
  (hB : B = ![3, 3, 5]) :
  deriv (λ t => u (A 0 + t * (12 / 13)) (A 1 + t * (-3 / 13)) (A 2 + t * (-4 / 13)))
    0 = -1 ∧
  deriv (λ t => u (B 0 + t * (12 / 13)) (B 1 + t * (-3 / 13)) (B 2 + t * (-4 / 13)))
    0 = 0 := by
  constructor
  · -- Calculate derivative at point A
    rw [hA]
    simp [hu]
    simp [deriv_const, deriv_id', deriv_add, deriv_mul, mul_comm]
    all_goals norm_num [deriv_pow]
  · -- Calculate derivative at point B
    rw [hB]
    simp [hu]
    simp [deriv_const, deriv_id', deriv_add, deriv_mul, mul_comm]
    all_goals norm_num [deriv_pow]