import Mathlib

theorem algebra_25888 {f : Polynomial ℤ} (hf : f.degree = 2)
    (h0 : f.eval 0 ≠ f.eval 3) (h1 : f.eval 3 ≠ f.eval 4) (h2 : f.eval 4 ≠ f.eval 0)
    (h3 : f.eval 0 = 2 ∨ f.eval 0 = 20 ∨ f.eval 0 = 202 ∨ f.eval 0 = 2022)
    (h4 : f.eval 3 = 2 ∨ f.eval 3 = 20 ∨ f.eval 3 = 202 ∨ f.eval 3 = 2022)
    (h5 : f.eval 4 = 2 ∨ f.eval 4 = 20 ∨ f.eval 4 = 202 ∨ f.eval 4 = 2022) :
    f.eval 1 = -80 ∨ f.eval 1 = -990 := by
  have h6 : f.natDegree = 2 := by
    rw [Polynomial.natDegree_eq_of_degree_eq_some hf]
    all_goals linarith
  have h8 : f.eval 0 = f.coeff 0 := by
    simp [Polynomial.eval_eq_sum_range, h6, Finset.sum_range_succ, mul_zero, add_zero]
    <;> ring_nf <;> omega
  have h9 : f.eval 3 = 9 * f.coeff 2 + 3 * f.coeff 1 + f.coeff 0 := by
    rw [Polynomial.eval_eq_sum_range, h6]
    simp [Finset.sum_range_succ, mul_add, add_mul]
    <;> ring_nf <;> omega
  have h10 : f.eval 4 = 16 * f.coeff 2 + 4 * f.coeff 1 + f.coeff 0 := by
    rw [Polynomial.eval_eq_sum_range, h6]
    simp [Finset.sum_range_succ, mul_add, add_mul]
    <;> ring_nf <;> omega
  have h11 : f.eval 1 = 1 * f.coeff 2 + 1 * f.coeff 1 + f.coeff 0 := by
    rw [Polynomial.eval_eq_sum_range, h6]
    simp [Finset.sum_range_succ, mul_add, add_mul]
    <;> ring_nf <;> omega
  rcases h3 with h3 | h3 | h3 | h3 <;> rcases h4 with h4 | h4 | h4 | h4 <;> rcases h5 with h5 | h5 | h5 | h5
  <;> simp [h8] at h3
  <;> simp [h9] at h4
  <;> simp [h10] at h5
  <;> simp [h11] at *
  <;> omega