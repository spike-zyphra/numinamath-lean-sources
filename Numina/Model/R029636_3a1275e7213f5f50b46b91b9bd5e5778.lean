import Mathlib

theorem algebra_15389 {p : Polynomial ℝ} (hp : p.Monic) (hp' : p.natDegree = 4)
    (h1 : p.eval 1 = 2) (h2 : p.eval 2 = 5) (h3 : p.eval 3 = 10) (h4 : p.eval 4 = 17) :
    p.eval 5 = 50 := by
  have eq5 : p.eval 1 = (1 : ℝ) ^ 4 * p.coeff 4 + (1 : ℝ) ^ 3 * p.coeff 3 + (1 : ℝ) ^ 2 * p.coeff 2 + (1 : ℝ) * p.coeff 1 + p.coeff 0 := by
    simp [Polynomial.eval_eq_sum_range, hp', Finset.sum_range_succ]
    <;> ring_nf
  have eq6 : p.eval 2 = (2 : ℝ) ^ 4 * p.coeff 4 + (2 : ℝ) ^ 3 * p.coeff 3 + (2 : ℝ) ^ 2 * p.coeff 2 + (2 : ℝ) * p.coeff 1 + p.coeff 0 := by
    simp [Polynomial.eval_eq_sum_range, hp', Finset.sum_range_succ]
    <;> ring_nf
  have eq7 : p.eval 3 = (3 : ℝ) ^ 4 * p.coeff 4 + (3 : ℝ) ^ 3 * p.coeff 3 + (3 : ℝ) ^ 2 * p.coeff 2 + (3 : ℝ) * p.coeff 1 + p.coeff 0 := by
    simp [Polynomial.eval_eq_sum_range, hp', Finset.sum_range_succ]
    <;> ring_nf
  have eq8 : p.eval 4 = (4 : ℝ) ^ 4 * p.coeff 4 + (4 : ℝ) ^ 3 * p.coeff 3 + (4 : ℝ) ^ 2 * p.coeff 2 + (4 : ℝ) * p.coeff 1 + p.coeff 0 := by
    simp [Polynomial.eval_eq_sum_range, hp', Finset.sum_range_succ]
    <;> ring_nf
  have eq9 : p.eval 5 = (5 : ℝ) ^ 4 * p.coeff 4 + (5 : ℝ) ^ 3 * p.coeff 3 + (5 : ℝ) ^ 2 * p.coeff 2 + (5 : ℝ) * p.coeff 1 + p.coeff 0 := by
    simp [Polynomial.eval_eq_sum_range, hp', Finset.sum_range_succ]
    <;> ring_nf
  have eq12 : p.coeff 4 = 1 := by
    have h1 : p.Monic := hp
    have h1' : p.leadingCoeff = 1 := by 
      simpa using h1
    have h1'2 : p.natDegree = 4 := hp'
    rw [Polynomial.leadingCoeff] at h1'
    rw [h1'2] at h1'
    linarith
  rw [eq5] at h1 
  rw [eq6] at h2
  rw [eq7] at h3 
  rw [eq8] at h4 
  rw [eq9] 
  nlinarith