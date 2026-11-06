import Mathlib

open Real

theorem inequalities_137523 (n : ℕ) (x : Fin n → ℝ)
    (h₀ : ∀ i, 0 ≤ x i) (h₁ : ∑ i, x i = n) :
    ∑ i, x i / (1 + x i ^ 2) ≤ ∑ i, 1 / (1 + x i) := by

  have h2 : ∀ i, 0 ≤ x i := h₀

  have h3 : ∀ i, x i / (1 + (x i) ^ 2) ≤ 1 / (1 + x i) - (1 - x i) / 4 := by
    intro i
    have h2i : 0 ≤ x i := h2 i
    have h4 : x i / (1 + (x i) ^ 2) ≤ 1 / (1 + x i) - (1 - x i) / 4 := by
      have h5 : 0 < (1 + x i) := by linarith
      have h6 : 0 < (1 + (x i) ^ 2) := by
        have h7 : (x i) ^ 2 ≥ 0 := sq_nonneg (x i)
        linarith
      have h7 : x i / (1 + (x i) ^ 2) - (1 / (1 + x i) - (1 - x i) / 4) ≤ 0 := by
        have h8 : x i / (1 + (x i) ^ 2) - (1 / (1 + x i) - (1 - x i) / 4) =
            (4 * (x i) * (1 + x i) - 4 * (1 + (x i) ^ 2) + (1 - x i) * (1 + x i) * (1 + (x i) ^ 2)) / (4 * (1 + x i) * (1 + (x i) ^ 2)) := by 
          field_simp
          ring
        rw [h8] at *
        have h9 : 4 * (1 + x i) * (1 + (x i) ^ 2) > 0 := by
          positivity
        have h10 : 4 * (x i) * (1 + x i) - 4 * (1 + (x i) ^ 2) + (1 - x i) * (1 + x i) * (1 + (x i) ^ 2) ≤ 0 := by
          nlinarith [sq_nonneg (x i - 1), sq_nonneg (x i ^ 2 - 1), sq_nonneg (x i * (x i - 1)), sq_nonneg ((x i) ^ 2 - 1), sq_nonneg (x i), sq_nonneg ((x i - 1) ^ 2), sq_nonneg ((x i) ^ 2 - x i), sq_nonneg ((x i) ^ 2 - x i), sq_nonneg ((x i) ^ 2 - 1), sq_nonneg ((x i) - 1)]
        apply div_nonpos_of_nonpos_of_nonneg h10 (by positivity)
      linarith
    linarith

  have h4 : ∑ i, x i / (1 + (x i) ^ 2) ≤ ∑ i, (1 / (1 + x i) - (1 - x i) / 4) := by
    apply Finset.sum_le_sum
    intro i _
    specialize h3 i
    linarith

  have h5 : ∑ i, (1 / (1 + x i) - (1 - x i) / 4) = ∑ i, 1 / (1 + x i) := by
    have h6 : ∑ i, (1 / (1 + x i) - (1 - x i) / 4) = ∑ i, (1 / (1 + x i)) - ∑ i, ((1 - x i) / 4) := by
      rw [Finset.sum_sub_distrib]
    rw [h6]
    have h7 : ∑ i, ((1 - x i) / 4) = 0 := by
      have h8 : ∑ i, ((1 - x i) / 4) = (∑ i, (1 - x i)) / 4 := by
        rw [Finset.sum_div]
      rw [h8]
      have h9 : ∑ i, (1 - x i) = (0 : ℝ) := by
        calc
          ∑ i, (1 - x i) = ∑ i : Fin n, (1 : ℝ) - ∑ i, x i := by
            rw [Finset.sum_sub_distrib]
          _ = (↑n : ℝ) - ∑ i, x i := by
            simp [Finset.sum_const, Finset.card_univ]
          _ = (↑n : ℝ) - (↑n : ℝ) := by 
            rw [h₁]
          _ = (0 : ℝ) := by 
            ring
      linarith
    linarith

  linarith [h4, h5]