import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_600545 {n : ℕ} (a : Fin n → ℝ)
  (ha : ∀ i, 0 < a i) (h : ∀ i, a i ≤ 2) (hsum : ∑ i, a i = n) :
  ∑ i, (a i)^2 ≤ 2 * n + 1 := by
  have h1 : ∀ i, (a i) ^ 2 ≤ 2 * (a i) := by
    intro i
    have h2 : a i ≤ 2 := h i
    have h3 : 0 < a i := ha i
    nlinarith [sq_nonneg (a i - 1)]
  have h2 : ∑ i, (a i) ^ 2 ≤ ∑ i, (2 * (a i)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact h1 i
  have h3 : ∑ i, (2 * (a i)) = 2 * (∑ i, (a i)) := by
    simp [Finset.mul_sum]
    <;> ring
  have h4 : ∑ i, (a i) = (n : ℝ) := by
    exact_mod_cast hsum
  rw [h3] at h2
  rw [h4] at h2
  norm_num at h2 ⊢
  linarith