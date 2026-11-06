import Mathlib

theorem algebra_321260 {F : Polynomial ℝ} (hF : F.degree = 5)
    (hF1 : F.eval (-2) = 0) (hF2 : F.eval (-1) = 0) (hF3 : F.eval 0 = 0)
    (hF4 : F.eval 1 = 0) (hF5 : F.eval 2 = 24) (hF6 : F.eval 3 = 360) :
    F.eval 4 = 1800 := by
  have h1 : F.natDegree = 5 := by
    rw [Polynomial.natDegree_eq_of_degree_eq_some hF]
  
  have eq1' : F.eval (-2) = 0 := hF1
  have eq2' : F.eval (-1) = 0 := hF2
  have eq3' : F.eval 0 = 0 := hF3
  have eq4' : F.eval 1 = 0 := hF4
  have eq5' : F.eval 2 = 24 := hF5
  have eq6' : F.eval 3 = 360 := hF6

  simp [Polynomial.eval_eq_sum_range, h1, Finset.sum_range_succ] at eq1' eq2' eq3' eq4' eq5' eq6' ⊢
  ring_nf at eq1' eq2' eq3' eq4' eq5' eq6' ⊢

  nlinarith [sq_nonneg (F.coeff 1 - 0), sq_nonneg (F.coeff 4 - 21), sq_nonneg (F.coeff 2), sq_nonneg (F.coeff 3 + 10), sq_nonneg (F.coeff 5 - 3)]