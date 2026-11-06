import Mathlib

open Real
open scoped BigOperators

theorem calculus_22858 (a b : Fin 3 → ℝ) :
  ∃ k, crossProduct (5 * a + 7 * b) (-a + 3 * b) = k * crossProduct a b := by
  use 22
  funext i
  fin_cases i <;> simp [crossProduct, Fin.sum_univ_three, add_mul, mul_add, mul_comm, mul_assoc]
  <;> ring