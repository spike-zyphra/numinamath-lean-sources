import Mathlib

open Real Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_173868 (α : ℝ) (a : ℕ → ℂ) (ha : ∀ n, a n = exp (I * n * α)) :
    ∃ r, ∀ n, a n = r ^ n ∧ ‖r‖ = 1 := by
  use exp (I * α)
  intro n
  constructor
  · -- Show that $a_n = r^n$.
    rw [ha n]
    have h : exp (I * n * α) = (exp (I * α)) ^ n := by
      rw [← Complex.exp_nat_mul]
      ring_nf
    rw [h]
  · -- Show that ‖r‖ = 1.
    have h1 : ‖exp (I * α)‖ = 1 := by
      rw [Complex.norm_eq_abs]
      rw [Complex.abs_exp]
      simp
    exact h1