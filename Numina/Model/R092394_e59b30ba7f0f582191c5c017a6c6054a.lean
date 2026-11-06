import Mathlib

theorem algebra_324910 {f : Polynomial ℝ} (hf : f.degree = 4)
    (h1 : f.eval 1 = 0) (h2 : f.eval 2 = 0) (h3 : f.eval 3 = 0)
    (h4 : f.eval 4 = 6) (h5 : f.eval 5 = 72) : f.eval 6 = 300 := by 
  have h6 : f.natDegree = 4 := by 
    rw [Polynomial.natDegree_eq_of_degree_eq_some hf]
    all_goals linarith
  
  have eq6 : f.eval 1 = f.coeff 0 + f.coeff 1 * 1 + f.coeff 2 * 1^2 + f.coeff 3 * 1^3 + f.coeff 4 * 1^4 := by
    rw [Polynomial.eval_eq_sum_range]
    simp [h6, Finset.sum_range_succ]
    <;> ring_nf <;> simp
    <;> linarith

  have eq7 : f.eval 2 = f.coeff 0 + f.coeff 1 * 2 + f.coeff 2 * 2^2 + f.coeff 3 * 2^3 + f.coeff 4 * 2^4 := by
    rw [Polynomial.eval_eq_sum_range]
    simp [h6, Finset.sum_range_succ]
    <;> ring_nf <;> simp
    <;> linarith

  have eq8 : f.eval 3 = f.coeff 0 + f.coeff 1 * 3 + f.coeff 2 * 3^2 + f.coeff 3 * 3^3 + f.coeff 4 * 3^4 := by
    rw [Polynomial.eval_eq_sum_range]
    simp [h6, Finset.sum_range_succ]
    <;> ring_nf <;> simp
    <;> linarith

  have eq9 : f.eval 4 = f.coeff 0 + f.coeff 1 * 4 + f.coeff 2 * 4^2 + f.coeff 3 * 4^3 + f.coeff 4 * 4^4 := by
    rw [Polynomial.eval_eq_sum_range]
    simp [h6, Finset.sum_range_succ]
    <;> ring_nf <;> simp
    <;> linarith

  have eq10 : f.eval 5 = f.coeff 0 + f.coeff 1 * 5 + f.coeff 2 * 5^2 + f.coeff 3 * 5^3 + f.coeff 4 * 5^4 := by
    rw [Polynomial.eval_eq_sum_range]
    simp [h6, Finset.sum_range_succ]
    <;> ring_nf <;> simp
    <;> linarith

  have eq11 : f.eval 6 = f.coeff 0 + f.coeff 1 * 6 + f.coeff 2 * 6^2 + f.coeff 3 * 6^3 + f.coeff 4 * 6^4 := by
    rw [Polynomial.eval_eq_sum_range]
    simp [h6, Finset.sum_range_succ]
    <;> ring_nf <;> simp
    <;> linarith
  
  rw [eq6] at h1
  rw [eq7] at h2
  rw [eq8] at h3
  rw [eq9] at h4
  rw [eq10] at h5
  rw [eq11] at *
  
  norm_num at h1 h2 h3 h4 h5 ⊢
  linarith