import Mathlib

theorem algebra_13374 {P : Polynomial ℝ} (hP : P.degree = 2)
    (hP2 : P.eval 2 = 10) (hP3 : P.eval 3 = 23) (hP4 : P.eval 4 = 40) :
    P.eval 1 = 1 := by
  have h2 : P.natDegree = 2 := by
    rw [Polynomial.natDegree_eq_of_degree_eq_some hP]
    all_goals try simp
    <;> linarith
  have eq1 : P.eval 2 = 4 * (P.coeff 2) + 2 * (P.coeff 1) + (P.coeff 0) := by
    rw [Polynomial.eval_eq_sum_range, h2]
    simp [Finset.sum_range_succ, pow_two]
    all_goals ring
  have eq2 : P.eval 3 = 9 * (P.coeff 2) + 3 * (P.coeff 1) + (P.coeff 0) := by
    rw [Polynomial.eval_eq_sum_range, h2]
    simp [Finset.sum_range_succ, pow_two]
    all_goals ring
  have eq3 : P.eval 4 = 16 * (P.coeff 2) + 4 * (P.coeff 1) + (P.coeff 0) := by
    rw [Polynomial.eval_eq_sum_range, h2]
    simp [Finset.sum_range_succ, pow_two]
    all_goals ring

  have hA : P.coeff 2 = 2 := by
    linarith [hP2, hP3, hP4, eq1, eq2, eq3]
  
  have hB : P.coeff 1 = 3 := by
    linarith [hP2, hP3, hP4, hA, eq1, eq2, eq3]

  have hC : P.coeff 0 = -4 := by
    linarith [hP2, hP3, hP4, hA, hB, eq1, eq2, eq3]

  have eq4 : P.eval 1 = 1 * (P.coeff 2) * (1 ^ 2) + 1 * (P.coeff 1) * (1 ^ 1) + (P.coeff 0) := by
    rw [Polynomial.eval_eq_sum_range, h2]
    simp [Finset.sum_range_succ, pow_two]
    all_goals ring

  rw [eq4]
  rw [hA, hB, hC]
  norm_num
  all_goals try linarith