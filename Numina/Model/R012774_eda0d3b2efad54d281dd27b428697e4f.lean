import Mathlib

theorem algebra_64112 {p : Polynomial ℝ} (hp : p.degree = 4)
    (h1 : p.coeff 4 = 1) (h2 : p.eval 1 = 1) (h3 : p.eval 2 = 2) (h4 : p.eval 3 = 3)
    (h5 : p.eval 4 = 4) : p.eval 5 = 29 := by
  have h6 : p.natDegree = 4 := by
    rw [Polynomial.natDegree_eq_of_degree_eq_some hp]
    all_goals linarith
  have eq1 := h2
  simp [Polynomial.eval_eq_sum_range, h6, Finset.sum_range_succ, h1] at eq1
  have eq2 := h3
  simp [Polynomial.eval_eq_sum_range, h6, Finset.sum_range_succ, h1] at eq2
  have eq3 := h4
  simp [Polynomial.eval_eq_sum_range, h6, Finset.sum_range_succ, h1] at eq3
  have eq4 := h5
  simp [Polynomial.eval_eq_sum_range, h6, Finset.sum_range_succ, h1] at eq4
  have eq5 : p.eval 5 = 29 := by
    simp [Polynomial.eval_eq_sum_range, h6, Finset.sum_range_succ, h1]
    ring_nf at eq1 eq2 eq3 eq4 ⊢
    linarith
  linarith [eq5]