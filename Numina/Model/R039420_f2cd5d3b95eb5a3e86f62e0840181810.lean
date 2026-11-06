import Mathlib

theorem algebra_322157 {t : Fin 3 → ℝ} (ht : ∀ i, t i ≠ 0)
    (h : ∑ i, t i / abs (t i) = 1) :
    abs (t 0 * t 1 * t 2) / (t 0 * t 1 * t 2) = -1 := by
  have h1 : t 0 / abs (t 0) + t 1 / abs (t 1) + t 2 / abs (t 2) = 1 := by 
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h ⊢
    linarith
  have h2 : t 0 / abs (t 0) = 1 ∨ t 0 / abs (t 0) = -1 := by
    cases le_or_lt 0 (t 0) with
    | inl h3 =>
      have h3' : abs (t 0) = t 0 := abs_of_nonneg h3
      left
      rw [h3']
      have h00 : t 0 ≠ 0 := ht 0
      field_simp [h00]
    | inr h4 =>
      have h4' : abs (t 0) = -t 0 := abs_of_neg h4
      right
      rw [h4']
      have h00 : t 0 ≠ 0 := ht 0
      field_simp [h00]
  have h3 : t 1 / abs (t 1) = 1 ∨ t 1 / abs (t 1) = -1 := by
    cases le_or_lt 0 (t 1) with
    | inl h3 =>
      have h3' : abs (t 1) = t 1 := abs_of_nonneg h3
      left
      rw [h3']
      have h00 : t 1 ≠ 0 := ht 1
      field_simp [h00]
    | inr h4 =>
      have h4' : abs (t 1) = -t 1 := abs_of_neg h4
      right
      rw [h4']
      have h00 : t 1 ≠ 0 := ht 1
      field_simp [h00]
  have h4 : t 2 / abs (t 2) = 1 ∨ t 2 / abs (t 2) = -1 := by
    cases le_or_lt 0 (t 2) with
    | inl h3 =>
      have h3' : abs (t 2) = t 2 := abs_of_nonneg h3
      left
      rw [h3']
      have h00 : t 2 ≠ 0 := ht 2
      field_simp [h00]
    | inr h4 =>
      have h4' : abs (t 2) = -t 2 := abs_of_neg h4
      right
      rw [h4']
      have h00 : t 2 ≠ 0 := ht 2
      field_simp [h00]
  -- We need to find the number of negatives.
  have h5 : (t 0 / abs (t 0) : ℝ) + (t 1 / abs (t 1) : ℝ) + (t 2 / abs (t 2) : ℝ) = 1 := h1
  have h6 : (t 0 / abs (t 0) : ℝ) = 1 ∧ (t 1 / abs (t 1) : ℝ) = 1 ∧ (t 2 / abs (t 2) : ℝ) = -1 ∨ 
      (t 0 / abs (t 0) : ℝ) = 1 ∧ (t 1 / abs (t 1) : ℝ) = -1 ∧ (t 2 / abs (t 2) : ℝ) = 1 ∨
      (t 0 / abs (t 0) : ℝ) = -1 ∧ (t 1 / abs (t 1) : ℝ) = 1 ∧ (t 2 / abs (t 2) : ℝ) = 1 := by
    rcases h2 with (h2 | h2) <;> rcases h3 with (h3 | h3) <;> rcases h4 with (h4 | h4) <;> 
      try { 
        norm_num [h2, h3, h4] at h5 ⊢ 
      } 
  -- Compute the product.
  have h7 : abs (t 0 * t 1 * t 2) / (t 0 * t 1 * t 2) = -1 := by
    have h8 : abs (t 0 * t 1 * t 2) / (t 0 * t 1 * t 2) = 1 / ((t 0 / abs (t 0)) * (t 1 / abs (t 1)) * (t 2 / abs (t 2))) := by
      have h7 : abs (t 0 * t 1 * t 2) = abs (t 0) * abs (t 1) * abs (t 2) := by
        simp [abs_mul]
      have h8 : abs (t 0 * t 1 * t 2) / (t 0 * t 1 * t 2) = (abs (t 0) * abs (t 1) * abs (t 2)) / (t 0 * t 1 * t 2) := by
        rw [h7]
      have h9 : (abs (t 0) * abs (t 1) * abs (t 2)) / (t 0 * t 1 * t 2) = abs (t 0) / t 0 * (abs (t 1) / t 1) * (abs (t 2) / t 2) := by
        field_simp [ht 0, ht 1, ht 2]
        all_goals ring
      have h10 : abs (t 0) / t 0 = 1 / (t 0 / abs (t 0)) := by
        have h10 : t 0 ≠ 0 := ht 0
        field_simp [h10]
      have h11 : abs (t 1) / t 1 = 1 / (t 1 / abs (t 1)) := by
        have h10 : t 1 ≠ 0 := ht 1
        field_simp [h10]
      have h12 : abs (t 2) / t 2 = 1 / (t 2 / abs (t 2)) := by
        have h10 : t 2 ≠ 0 := ht 2
        field_simp [h10]
      rw [h8, h9, h10, h11, h12]
      all_goals field_simp
    rw [h8]
    rcases h6 with (h6 | h6 | h6)
    · -- case 1, 1, -1
      rw [h6.1, h6.2.1, h6.2.2]
      norm_num
    · -- case 1, -1, 1
      rw [h6.1, h6.2.1, h6.2.2]
      norm_num
    · -- case -1, 1, 1
      rw [h6.1, h6.2.1, h6.2.2]
      norm_num
  exact h7