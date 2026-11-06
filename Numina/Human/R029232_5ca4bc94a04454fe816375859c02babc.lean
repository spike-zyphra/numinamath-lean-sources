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
  rw [hA]
  have h1 : deriv (λ t => u (0 + t * (12 / 13)) (-2 + t * (-3 / 13)) (-1 + t * (-4 / 13)))
    0 = -1 := by
    rw [hu]
    simp [deriv_add, deriv_mul, deriv_const, add_assoc, mul_comm, mul_assoc]
    <;> norm_num
  rw [hB]
  have h2 : deriv (λ t => u (3 + t * (12 / 13)) (3 + t * (-3 / 13)) (5 + t * (-4 / 13)))
    0 = 0 := by
    rw [hu]
    simp [deriv_add, deriv_mul, deriv_const, add_assoc, mul_comm, mul_assoc]
    <;> norm_num
  exact ⟨h1, h2⟩