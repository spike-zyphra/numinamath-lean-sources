import Mathlib

theorem inequalities_1637 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    (∑ i, (a i)^5) + 4 * n ≥ 5 * ∑ i, a i := by
  have h1 : ∀ i : Fin n, (a i) ^ 5 + 4 ≥ 5 * (a i) := by
    intro i
    have h2 : 0 ≤ a i := ha i
    nlinarith [sq_nonneg ((a i) ^ 2 - 1), sq_nonneg ((a i) - 1), sq_nonneg ((a i) ^ 2 - (a i)), sq_nonneg ((a i) + 1), sq_nonneg ((a i) - 2), sq_nonneg ((a i) ^ 2 - 4), sq_nonneg ((a i) ^ 3 - (a i) ^ 2), sq_nonneg ((a i) ^ 2 - (a i) + 1), sq_nonneg ((a i) ^ 2 + (a i) - 2), mul_nonneg (show (0 : ℝ) ≤ (a i) by linarith) (show (0 : ℝ) ≤ (a i) by linarith)]
  have h2 : (∑ i : Fin n, (a i) ^ 5) + 4 * n ≥ 5 * (∑ i : Fin n, (a i)) := by
    have h3 : ∀ i : Fin n, (a i) ^ 5 + 4 ≥ 5 * (a i) := h1
    have h4 : ∑ i : Fin n, ((a i) ^ 5 + 4) ≥ ∑ i : Fin n, (5 * (a i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have h5 : (a i) ^ 5 + 4 ≥ 5 * (a i) := h3 i
      linarith
    have eq1 : ∑ i : Fin n, ((a i) ^ 5 + 4) = (∑ i : Fin n, (a i) ^ 5) + 4 * n := by
      rw [Finset.sum_add_distrib]
      simp [Finset.mul_sum]
      <;> ring
    have eq2 : ∑ i : Fin n, (5 * (a i)) = 5 * (∑ i : Fin n, (a i)) := by
      simp [Finset.mul_sum]
      <;> ring
    linarith [eq1, eq2, h4]
  linarith [h2]