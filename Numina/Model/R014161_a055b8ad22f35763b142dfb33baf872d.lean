import Mathlib

theorem inequalities_224803 (n : ℕ) (f : Fin n → ℝ) (h₀ : ∀ i, -1 ≤ f i ∧ f i ≤ 1)
    (h₁ : ∑ i, (f i)^3 = 0) : ∑ i, f i ≤ n / 3 := by
  have h6 : ∀ i : Fin n, 3 * (f i) - 4 * ((f i)^3) ≤ 1 := by
    intro i
    have h3 : -1 ≤ f i := (h₀ i).left
    have h4 : f i ≤ 1 := (h₀ i).right
    nlinarith [sq_nonneg ((f i) - 1/2), sq_nonneg ((f i) + 1), sq_nonneg ((f i) - 1), sq_nonneg ((f i)^2 - (1/4)), sq_nonneg ((f i)^2 -1), mul_nonneg (show (0 : ℝ) ≤ f i + 1 by linarith) (show (0 : ℝ) ≤ 1 - f i by linarith), sq_nonneg ((f i)^3 - (f i)/2), sq_nonneg ((f i)*(f i) - f i/2), sq_nonneg (((f i) + 1) * (f i - 1))]
  have h8 : ∑ i : Fin n, (3 * (f i) - 4 * ((f i)^3)) ≤ (n : ℝ) := by
    have h6' : ∀ i : Fin n, 3 * (f i) - 4 * ((f i)^3) ≤ (1 : ℝ) := by
      intro i
      specialize h6 i
      linarith
    have h7 : ∑ i : Fin n, (3 * (f i) - 4 * ((f i)^3)) ≤ ∑ i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      specialize h6' i
      linarith
    have h8' : ∑ i : Fin n, (1 : ℝ) = (n : ℝ) := by
      simp
    linarith [h7, h8']
  have h9 : ∑ i : Fin n, (3 * (f i) - 4 * ((f i)^3)) = 3 * (∑ i : Fin n, (f i : ℝ)) - 4 * (∑ i : Fin n, ((f i : ℝ) ^ 3)) := by
    simp [Finset.sum_sub_distrib, Finset.mul_sum]
    <;> ring_nf <;> simp [Finset.sum_mul]
    all_goals linarith
  have h11 : 3 * (∑ i : Fin n, (f i : ℝ)) - 4 * (∑ i : Fin n, ((f i : ℝ) ^ 3)) ≤ (n : ℝ) := by
    linarith [h8, h9]
  rw [h₁] at h11
  have h10 : 3 * (∑ i : Fin n, (f i : ℝ)) ≤ (n : ℝ) := by linarith
  have h12 : ∑ i : Fin n, (f i : ℝ) ≤ (n / 3 : ℝ) := by
    linarith
  have h13 : ∑ i : Fin n, f i ≤ (n / 3 : ℝ) := by
    simpa using h12
  simpa using h13