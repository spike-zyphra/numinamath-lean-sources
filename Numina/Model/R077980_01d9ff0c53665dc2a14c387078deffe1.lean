import Mathlib

theorem inequalities_81963 (n : ℕ) (x : Fin n → ℝ)
    (h₁ : ∀ i, -1 ≤ x i) (h₂ : ∑ i, (x i)^3 = 0) :
    ∑ i, x i ≤ n / 3 := by
  have h3 : ∀ i, (x i)^3 ≥ (3 / 4) * (x i) - (1 / 4) := by
    intro i
    have h4 : -1 ≤ x i := h₁ i
    have h5 : (x i)^3 - (3 / 4) * (x i) + (1 / 4) ≥ 0 := by
      nlinarith [sq_nonneg (x i - 1 / 2), sq_nonneg (x i + 1), h4]
    linarith
  have h6 : ∑ i, (x i)^3 ≥ ∑ i, ((3 / 4) * (x i) - (1 / 4)) := by
    apply Finset.sum_le_sum
    intro i hi
    have h3' := h3 i
    linarith
  have h7 : ∑ i, ((3 / 4) * (x i) - (1 / 4)) ≤ (0 : ℝ) := by
    linarith [h₂, h6]
  have h8 : ∑ i, ((3 / 4) * (x i) - (1 / 4)) = (3 / 4) * (∑ i, x i) - (n : ℝ) / 4 := by
    simp [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    <;> ring
  rw [h8] at h7
  linarith