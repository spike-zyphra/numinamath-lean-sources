import Mathlib

theorem inequalities_201456 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = 10) (hsumsq : ∑ i, (a i)^2 > 20) :
    ∑ i, (a i)^3 > 40 := by
  have h1 : ∀ i, (a i) ^ 3 ≥ 4 * (a i) ^ 2 - 4 * (a i) := by
    intro i
    have h2 : 0 < a i := ha i
    nlinarith [sq_nonneg ((a i) - 2)]
  have h2 : ∑ i, (a i) ^ 3 ≥ ∑ i, (4 * (a i) ^ 2 - 4 * (a i)) := by
    apply Finset.sum_le_sum
    intro i hi
    specialize h1 i
    linarith
  have h3 : ∑ i, (4 * (a i) ^ 2 - 4 * (a i)) = 4 * (∑ i, (a i) ^ 2) - 4 * (∑ i, (a i)) := by
    simp [Finset.sum_sub_distrib, Finset.mul_sum]
    <;> ring
  -- Use h3 to rewrite and then prove the final result
  have h4 : ∑ i, (a i) ^ 3 > (40 : ℝ) := by
    have h5 : ∑ i, (4 * (a i) ^ 2 - 4 * (a i)) > (40 : ℝ) := by
      have h6 : ∑ i, (4 * (a i) ^ 2 - 4 * (a i)) = 4 * (∑ i, (a i) ^ 2) - 4 * (∑ i, (a i)) := h3
      rw [h6]
      nlinarith [hsum, hsumsq]
    linarith [h2, h5]
  exact h4