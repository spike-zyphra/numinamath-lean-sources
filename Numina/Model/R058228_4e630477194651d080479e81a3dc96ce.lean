import Mathlib

theorem inequalities_215553 (n : ℕ) (f : Fin n → ℝ)
    (h₀ : ∀ i, f i ∈ Set.Icc (-1) 1) (h₁ : ∑ i, f i ^ 3 = 0) :
    ∑ i, f i ≤ n / 3 := by
  have h2 (i : Fin n) : f i ≤ 1 := by
    have h_i := h₀ i
    simp at h_i ⊢
    exact h_i.2
  have h3 (i : Fin n) : -1 ≤ f i := by
    have h_i := h₀ i
    simp at h_i ⊢
    exact h_i.1
  have h4 : ∑ i, f i ≤ n / 3 := by
    have h5 : ∀ i : Fin n, f i ^ 3 ≥ (3 / 4) * (f i) - (1 / 4) := by
      intro i
      have h_f := h₀ i
      simp at h_f ⊢
      nlinarith [sq_nonneg (f i - 1), sq_nonneg (f i + 1), sq_nonneg (f i - (1 / 2)), sq_nonneg (f i - (1 / 4) * 3)]
    have h6 : ∑ i, f i ^ 3 ≥ (3 / 4) * ∑ i, f i - (1 / 4) * n := by
      calc
        ∑ i, f i ^ 3 ≥ ∑ i, ((3 / 4) * (f i) - (1 / 4)) := by
          apply Finset.sum_le_sum
          intro i hi
          specialize h5 i
          linarith
        _ = (3 / 4) * ∑ i, f i - (1 / 4) * n := by
          simp [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
          <;> ring
    have h7 : 0 ≥ (3 / 4) * ∑ i, f i - (1 / 4) * n := by linarith [h₁, h6]
    have h8 : ∑ i, f i ≤ (n : ℝ) / 3 := by
      linarith
    linarith
  exact h4