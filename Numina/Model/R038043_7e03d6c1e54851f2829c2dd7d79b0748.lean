import Mathlib

open Polynomial

theorem algebra_16991 {p : ℝ[X]} (h : p.degree = 3) (h1 : p.eval 1 = -7) (h2 : p.eval 2 = -9) (h3 : p.eval 3 = -15) (h4 : p.eval 4 = -31) :
    p = -X ^ 3 + 4 * X ^ 2 - 7 * X - 3 := by
  have h5 : p.natDegree = 3 := by 
    rw [natDegree_eq_of_degree_eq_some h]
    all_goals norm_num
  have eq1 := h1
  simp [Polynomial.eval_eq_sum_range, h5, Finset.sum_range_succ] at eq1
  have eq2 := h2
  simp [Polynomial.eval_eq_sum_range, h5, Finset.sum_range_succ] at eq2
  have eq3 := h3
  simp [Polynomial.eval_eq_sum_range, h5, Finset.sum_range_succ] at eq3
  have eq4 := h4
  simp [Polynomial.eval_eq_sum_range, h5, Finset.sum_range_succ] at eq4
  have eq5 : p.coeff 0 = -3 := by
    ring_nf at eq1 eq2 eq3 eq4
    linarith
  have eq6 : p.coeff 1 = -7 := by
    ring_nf at eq1 eq2 eq3 eq4
    linarith
  have eq7 : p.coeff 2 = 4 := by
    ring_nf at eq1 eq2 eq3 eq4
    linarith
  have eq8 : p.coeff 3 = -1 := by
    ring_nf at eq1 eq2 eq3 eq4
    linarith
  apply Polynomial.funext
  intro x
  have eq9 : p.eval x = p.coeff 0 + p.coeff 1 * x + p.coeff 2 * x^2 + p.coeff 3 * x^3 := by
    simp [Polynomial.eval_eq_sum_range, h5, Finset.sum_range_succ]
    <;> ring
  rw [eq9]
  simp [eq5, eq6, eq7, eq8]
  all_goals ring