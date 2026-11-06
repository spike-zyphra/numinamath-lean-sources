import Mathlib

open Real

theorem inequalities_598691 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ) :
    (∑ i : Fin n, a i) ^ 2 ≤ n * ∑ i : Fin n, (a i) ^ 2 := by

  have h4 : (∑ i : Fin n, a i) ^ 2 ≤ n * ∑ i : Fin n, (a i) ^ 2 := by
    have h5 : (∑ i : Fin n, a i) ^ 2 ≤ (∑ i : Fin n, (a i) ^ 2) * (∑ i : Fin n, (1 : ℝ) ^ 2) := by
      have h6 : (∑ i : Fin n, a i) = (∑ i : Fin n, (a i * (1 : ℝ)) ) := by
        simp [Finset.sum_congr]
      rw [h6]
      have h7 : (∑ i : Fin n, (a i * (1 : ℝ)) ) ^ 2 ≤ (∑ i : Fin n, (a i) ^ 2) * (∑ i : Fin n, (1 : ℝ) ^ 2) := by
        apply Finset.sum_mul_sq_le_sq_mul_sq 
      linarith
    have h8 : (∑ i : Fin n, (1 : ℝ) ^ 2) = (n : ℝ) := by 
      simp
    rw [h8] at h5 
    linarith 
  linarith