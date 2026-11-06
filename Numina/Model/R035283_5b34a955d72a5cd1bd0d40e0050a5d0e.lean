import Mathlib

theorem algebra_13934 {f : Polynomial ℝ} (hf : f.degree = 5)
    (h1 : f.eval 1 = 0) (h3 : f.eval 3 = 1) (h9 : f.eval 9 = 2)
    (h27 : f.eval 27 = 3) (h81 : f.eval 81 = 4) (h243 : f.eval 243 = 5) :
    f.coeff 1 = 121 / 162 := by
  have h2 : f.natDegree = 5 := by 
    rw [Polynomial.natDegree_eq_of_degree_eq_some hf]
    all_goals simp
  have eq1 : f.eval 1 = 0 := h1
  have eq2 : f.eval 3 = 1 := h3
  have eq3 : f.eval 9 = 2 := h9
  have eq4 : f.eval 27 = 3 := h27
  have eq5 : f.eval 81 = 4 := h81
  have eq6 : f.eval 243 = 5 := h243

  have eq1' : f.eval 1 = f.coeff 5 * (1:ℝ) ^ 5 + f.coeff 4 * (1:ℝ) ^ 4 + f.coeff 3 * (1:ℝ) ^ 3 + f.coeff 2 * (1:ℝ) ^ 2 + f.coeff 1 * (1:ℝ) ^ 1 + f.coeff 0 := by
    rw [Polynomial.eval_eq_sum_range' (show f.natDegree < (f.natDegree + 1) by omega)]
    simp [h2, Finset.sum_range_succ]
    <;> ring
  have eq2' : f.eval 3 = f.coeff 5 * (3:ℝ) ^ 5 + f.coeff 4 * (3:ℝ) ^ 4 + f.coeff 3 * (3:ℝ) ^ 3 + f.coeff 2 * (3:ℝ) ^ 2 + f.coeff 1 * (3:ℝ) ^ 1 + f.coeff 0 := by 
    rw [Polynomial.eval_eq_sum_range' (show f.natDegree < (f.natDegree + 1) by omega)]
    simp [h2, Finset.sum_range_succ]
    <;> ring
  have eq3' : f.eval 9 = f.coeff 5 * (9:ℝ) ^ 5 + f.coeff 4 * (9:ℝ) ^ 4 + f.coeff 3 * (9:ℝ) ^ 3 + f.coeff 2 * (9:ℝ) ^ 2 + f.coeff 1 * (9:ℝ) ^ 1 + f.coeff 0 := by 
    rw [Polynomial.eval_eq_sum_range' (show f.natDegree < (f.natDegree + 1) by omega)]
    simp [h2, Finset.sum_range_succ]
    <;> ring
  have eq4' : f.eval 27 = f.coeff 5 * (27:ℝ) ^ 5 + f.coeff 4 * (27:ℝ) ^ 4 + f.coeff 3 * (27:ℝ) ^ 3 + f.coeff 2 * (27:ℝ) ^ 2 + f.coeff 1 * (27:ℝ) ^ 1 + f.coeff 0 := by 
    rw [Polynomial.eval_eq_sum_range' (show f.natDegree < (f.natDegree + 1) by omega)]
    simp [h2, Finset.sum_range_succ]
    <;> ring
  have eq5' : f.eval 81 = f.coeff 5 * (81:ℝ) ^ 5 + f.coeff 4 * (81:ℝ) ^ 4 + f.coeff 3 * (81:ℝ) ^ 3 + f.coeff 2 * (81:ℝ) ^ 2 + f.coeff 1 * (81:ℝ) ^ 1 + f.coeff 0 := by 
    rw [Polynomial.eval_eq_sum_range' (show f.natDegree < (f.natDegree + 1) by omega)]
    simp [h2, Finset.sum_range_succ]
    <;> ring
  have eq6' : f.eval 243 = f.coeff 5 * (243:ℝ) ^ 5 + f.coeff 4 * (243:ℝ) ^ 4 + f.coeff 3 * (243:ℝ) ^ 3 + f.coeff 2 * (243:ℝ) ^ 2 + f.coeff 1 * (243:ℝ) ^ 1 + f.coeff 0 := by 
    rw [Polynomial.eval_eq_sum_range' (show f.natDegree < (f.natDegree + 1) by omega)]
    simp [h2, Finset.sum_range_succ]
    <;> ring
  rw [eq1'] at eq1
  rw [eq2'] at eq2
  rw [eq3'] at eq3
  rw [eq4'] at eq4
  rw [eq5'] at eq5
  rw [eq6'] at eq6
  ring_nf at eq1 eq2 eq3 eq4 eq5 eq6
  have eq7 : f.coeff 1 = 121 / 162 := by
    norm_num at eq1 eq2 eq3 eq4 eq5 eq6 ⊢
    linarith 
  exact_mod_cast eq7