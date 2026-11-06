import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_12719 {M : Set ℝ} (hM : M = {x | (x - 5) / (x + 1) < 0}) :
    (MeasureTheory.volume {x | x ∈ M ∧ logb 2 (x + 1) < 1}).toReal =
    (MeasureTheory.volume M).toReal / 3 := by
  have h1 : M = Set.Ioo (-1 : ℝ) (5 : ℝ) := by
    ext x
    simp [hM]
    constructor
    · -- Assume (x - 5) / (x + 1) < 0, prove x ∈ Ioo (-1, 5)
      intro h
      have : (x - 5) / (x + 1) < 0 := h
      apply div_neg_iff.mp at this
      cases this with
      | inl h1 =>
        linarith -- Impossible
      | inr h2 =>
        constructor <;> linarith
    · -- Assume x ∈ Ioo (-1, 5), prove (x - 5) / (x + 1) < 0
      rintro ⟨h1, h2⟩
      have h3 : x + 1 > 0 := by linarith
      have h4 : x - 5 < 0 := by linarith
      apply div_neg_of_neg_of_pos
      · linarith
      all_goals linarith
  have h2 : {x | x ∈ M ∧ logb 2 (x + 1) < 1} = Set.Ioo (-1 : ℝ) (1 : ℝ) := by
    ext x
    simp only [h1, Set.mem_setOf_eq, Set.mem_Ioo]
    constructor
    · -- Assume x ∈ M ∧ logb 2 (x + 1) < 1
      intro h
      rcases h with ⟨⟨h1, h2⟩, h3⟩
      have h4 : x + 1 > 0 := by linarith
      have h5 : logb 2 (x + 1) < 1 := h3
      have h6 : x + 1 < (2 : ℝ) := by
        by_contra h
        push_neg at h
        have h7 : logb 2 (x + 1) ≥ 1 := by
          have h8 : logb 2 (x + 1) = logb 2 (x + 1) := by rfl
          have h9 : logb 2 (x + 1) ≥ logb 2 (2 : ℝ) := by
            apply Real.logb_le_logb_of_le
            all_goals nlinarith
          have h10 : logb 2 (2 : ℝ) = 1 := by
            rw [Real.logb_self_eq_one]
            all_goals linarith
          nlinarith
        nlinarith
      constructor <;> linarith
    · -- Assume x ∈ Ioo (-1, 1)
      intro h
      rcases h with ⟨h1, h2⟩
      constructor
      · -- Show x ∈ M
        constructor
        · -- Show -1 < x
          linarith
        · -- Show x < 5
          linarith
      · -- Show logb 2 (x + 1) < 1
        have h4 : x + 1 > 0 := by linarith
        have h5 : x + 1 < (2 : ℝ) := by
          linarith
        have h6 : logb 2 (x + 1) < 1 := by
          have h7 : logb 2 (x + 1) < logb 2 (2 : ℝ) := by
            apply Real.logb_lt_logb
            all_goals nlinarith
          have h8 : logb 2 (2 : ℝ) = 1 := by
            rw [Real.logb_self_eq_one]
            all_goals linarith
          linarith
        simpa using h6
  rw [h2]
  rw [h1]
  simp
  all_goals
    norm_num