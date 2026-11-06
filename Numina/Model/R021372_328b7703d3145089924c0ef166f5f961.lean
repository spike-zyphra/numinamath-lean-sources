import Mathlib

theorem algebra_117708 {P : Polynomial ℝ} (hP : P.degree = 4)
    (hP0 : P.eval 0 = 1) (hP1 : P.eval 1 = 1) (hP2 : P.eval 2 = 4)
    (hP3 : P.eval 3 = 9) (hP4 : P.eval 4 = 16) :
    P.eval (-1) = 6 := by

  have h1 : P.natDegree = 4 := by
    rw [Polynomial.natDegree_eq_of_degree_eq_some hP]
    all_goals linarith

  have eq1 : P.eval 0 = 1 := hP0
  have eq2 : P.eval 1 = 1 := hP1
  have eq3 : P.eval 2 = 4 := hP2
  have eq4 : P.eval 3 = 9 := hP3
  have eq5 : P.eval 4 = 16 := hP4

  have eq1' : P.eval 0 = 1 := hP0

  rw [Polynomial.eval_eq_sum_range, h1] at eq1
  simp [Finset.sum_range_succ] at eq1

  rw [Polynomial.eval_eq_sum_range, h1] at eq2
  simp [Finset.sum_range_succ] at eq2

  rw [Polynomial.eval_eq_sum_range, h1] at eq3
  simp [Finset.sum_range_succ] at eq3

  rw [Polynomial.eval_eq_sum_range, h1] at eq4
  simp [Finset.sum_range_succ] at eq4

  rw [Polynomial.eval_eq_sum_range, h1] at eq5
  simp [Finset.sum_range_succ] at eq5

  have eq6 : P.eval (-1) = 6 := by
    rw [Polynomial.eval_eq_sum_range, h1]
    simp [Finset.sum_range_succ]
    ring_nf at eq1 eq2 eq3 eq4 eq5 ⊢
    linarith

  exact eq6