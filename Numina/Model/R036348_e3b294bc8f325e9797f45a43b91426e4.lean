import Mathlib

open Polynomial

theorem algebra_608764 {P: ℝ[X]} (h_deg: P.natDegree ≤ 3) (h1: P.eval 1 = 1 / (1 + 1 + 1 ^ 2))
  (h2: P.eval 2 = 1 / (1 + 2 + 2 ^ 2)) (h3: P.eval 3 = 1 / (1 + 3 + 3 ^ 2))
  (h4: P.eval 4 = 1 / (1 + 4 + 4 ^ 2)): P.eval 5 = - 3 / 91 := by

  have eq5 : P.natDegree ≤ 3 := h_deg
  have eq6 : ∀ (x : ℝ), P.eval x = (P.coeff 3) * x ^ 3 + (P.coeff 2) * x ^ 2 + (P.coeff 1) * x + (P.coeff 0) := by
    intro x
    rw [Polynomial.eval_eq_sum_range' (show P.natDegree < 4 by omega)]
    simp [Finset.sum_range_succ, pow_succ, mul_add]
    <;> ring

  have eq1' := eq6 1
  rw [eq1'] at h1

  have eq2' := eq6 2
  rw [eq2'] at h2

  have eq3' := eq6 3
  rw [eq3'] at h3

  have eq4' := eq6 4
  rw [eq4'] at h4

  have eq5' := eq6 5
  rw [eq5'] at *
  norm_num at h1 h2 h3 h4 ⊢
  linarith