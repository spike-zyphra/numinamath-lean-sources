import Mathlib

theorem calculus_23035 {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ∑ i, A i i = 2)
    (hA2 : ∑ i, (A ^ 2) i i = 30) : A.det = -13 := by
  have h1 : A 0 0 + A 1 1 = 2 := by 
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hA ⊢
    linarith
  have h2 : (A ^ 2) 0 0 + (A ^ 2) 1 1 = 30 := by
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hA2 ⊢
    linarith
  have eq1 : (A ^ 2) 0 0 = A 0 0 * A 0 0 + A 0 1 * A 1 0 := by 
    simp [pow_two, Matrix.mul_apply, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    <;> ring
  have eq2 : (A ^ 2) 1 1 = A 1 0 * A 0 1 + A 1 1 * A 1 1 := by 
    simp [pow_two, Matrix.mul_apply, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    <;> ring
  rw [eq1, eq2] at h2
  have h3 : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by 
    simp [Matrix.det_fin_two]
  have eq3 : (A 0 0 + A 1 1) ^ 2 - ((A 0 0) ^ 2 + 2 * (A 0 1 * A 1 0) + (A 1 1) ^ 2) = -26 := by 
    nlinarith
  have eq4 : 2 * (A.det) = -26 := by 
    have eq5 : 2 * (A.det) = (A 0 0 + A 1 1) ^ 2 - ((A 0 0) ^ 2 + 2 * (A 0 1 * A 1 0) + (A 1 1) ^ 2) := by
      rw [h3]
      all_goals
        nlinarith
    linarith [eq5, eq3]
  linarith