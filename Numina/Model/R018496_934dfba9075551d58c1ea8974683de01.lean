import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_275713 {M : Set ℝ} (hM : M = {x | (x - 5) / (x + 1) < 0}) :
    (MeasureTheory.volume {x | x ∈ M ∧ logb 2 (x + 1) < 1}).toReal =
    (MeasureTheory.volume M).toReal / 3 := by
  have h1 : M = Set.Ioo (-1 : ℝ) (5 : ℝ) := by
    ext x
    simp [hM]
    constructor
    · -- Assume (x - 5) / (x + 1) < 0, need to show -1 < x < 5
      intro h
      have h2 : x + 1 > 0 := by
        by_contra h2
        push_neg at h2
        have h3 : (x - 5) / (x + 1) ≥ 0 := by
          apply div_nonneg_of_nonpos
          · -- Show x - 5 ≤ 0
            have : x ≤ 5 := by nlinarith
            linarith
          · -- Show x + 1 ≤ 0
            linarith
        linarith
      have h4 : x - 5 < 0 := by
        have h5 : (x - 5) / (x + 1) < 0 := h
        apply (div_neg_iff).mp at h5
        cases h5 with
        | inl h1 =>
          linarith
        | inr h2 =>
          linarith
      constructor <;> linarith
    · -- Assume -1 < x < 5, need to show (x - 5) / (x + 1) < 0
      rintro ⟨h1, h2⟩
      have h3 : x + 1 > 0 := by linarith
      have h4 : x - 5 < 0 := by linarith
      apply div_neg_of_neg_of_pos
      · linarith
      · linarith
  have h2 : {x | x ∈ M ∧ logb 2 (x + 1) < 1} = Set.Ioo (-1 : ℝ) (1 : ℝ) := by
    ext x
    simp [h1]
    constructor
    · -- Assume x ∈ M and logb 2 (x + 1) < 1.
      rintro ⟨⟨hx1, hx2⟩, h3⟩
      have h4 : x + 1 > 0 := by linarith
      have h5 : logb 2 (x + 1) < 1 := h3
      have h6 : x + 1 < (2 : ℝ) := by
        by_contra h
        push_neg at h
        have h7 : logb 2 (x + 1) ≥ 1 := by
          have h8 : logb 2 (x + 1) = Real.logb 2 (x + 1) := by rfl
          rw [h8]
          have h9 : Real.logb 2 (x + 1) ≥ 1 := by
            have h10 : Real.logb 2 (x + 1) ≥ Real.logb 2 (2 : ℝ) := by
              apply Real.logb_le_logb_of_le
              all_goals linarith
            have h11 : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
            linarith [h11]
          linarith
        linarith
      have hx3 : x < (1 : ℝ) := by linarith
      constructor <;> linarith
    · -- Assume -1 < x < 1.
      rintro ⟨hx1, hx2⟩
      constructor
      · -- Show x ∈ M
        constructor <;> linarith
      · -- Show logb 2 (x + 1) < 1
        have h4 : x + 1 > 0 := by linarith
        have h5 : x + 1 < (2 : ℝ) := by linarith
        have h6 : logb 2 (x + 1) < 1 := by
          have h7 : logb 2 (x + 1) < logb 2 (2 : ℝ) := by
            apply Real.logb_lt_logb
            all_goals linarith
          have h8 : logb 2 (2 : ℝ) = 1 := by
            simp [logb_eq_iff_rpow_eq]
          linarith [h7, h8]
        linarith
  rw [h2]
  rw [h1]
  simp
  all_goals
    norm_num