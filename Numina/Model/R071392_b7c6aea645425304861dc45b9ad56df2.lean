import Mathlib

theorem inequalities_293974 (n : ℕ) (a : Fin n → ℝ)
    (h₀ : ∀ i, 0 < a i) (h₁ : ∑ i, a i = 10)
    (h₂ : ∑ i, (a i)^2 > 20) :
    ∑ i, (a i)^3 > 40 := by 
  have h3 : ∀ i, (a i) ^ 2 ≥ 4 * (a i) - 4 := by
    intro i
    nlinarith [sq_nonneg (a i - 2), h₀ i]

  have h4 : ∀ i, (a i) ^ 3 ≥ 4 * (a i) ^ 2 - 4 * (a i) := by
    intro i
    have h5 : (a i) ^ 2 ≥ 4 * (a i) - 4 := h3 i
    nlinarith [h5, h₀ i]

  have h6 : ∑ i, (a i) ^ 3 ≥ ∑ i, (4 * (a i) ^ 2 - 4 * (a i)) := by
    apply Finset.sum_le_sum
    intro i hi
    linarith [h4 i]

  have h7 : ∑ i, (4 * (a i) ^ 2 - 4 * (a i)) = 4 * (∑ i, (a i) ^ 2) - 4 * (∑ i, a i) := by
    rw [Finset.sum_sub_distrib]
    congr
    <;> rw [←Finset.mul_sum]

  rw [h7] at h6
  rw [h₁] at h6
  linarith [h₂, h6]