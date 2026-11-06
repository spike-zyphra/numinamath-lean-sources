import Mathlib

theorem algebra_100325 {P : Polynomial ℝ} (hP : P.degree = 4)
    (hP0 : P.eval 0 = 1) (hP1 : P.eval 1 = 1) (hP2 : P.eval 2 = 4)
    (hP3 : P.eval 3 = 9) (hP4 : P.eval 4 = 16) :
    P.eval (-2) = 19 := by 
  have h5 : P.natDegree = 4 := by 
    rw [Polynomial.natDegree_eq_of_degree_eq_some hP]
    all_goals simp
  have eq1 := hP0
  simp [Polynomial.eval_eq_sum_range, h5, Finset.sum_range_succ] at eq1
  have eq2 := hP1
  simp [Polynomial.eval_eq_sum_range, h5, Finset.sum_range_succ] at eq2
  have eq3 := hP2
  simp [Polynomial.eval_eq_sum_range, h5, Finset.sum_range_succ] at eq3
  have eq4 := hP3
  simp [Polynomial.eval_eq_sum_range, h5, Finset.sum_range_succ] at eq4
  have eq5 := hP4
  simp [Polynomial.eval_eq_sum_range, h5, Finset.sum_range_succ] at eq5
  -- proving $P(-2) = 19$
  simp [Polynomial.eval_eq_sum_range, h5, Finset.sum_range_succ]
  ring_nf at eq1 eq2 eq3 eq4 eq5 ⊢
  linarith