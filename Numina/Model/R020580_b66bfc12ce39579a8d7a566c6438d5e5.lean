import Mathlib

open Real Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_227807 (φ : ℝ) (n : ℕ) :
  (exp (I * φ))^n = exp (I * n * φ) := by 
  rw [← Complex.exp_nat_mul]
  all_goals ring_nf
  <;> simp [mul_comm]