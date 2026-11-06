import Mathlib

theorem algebra_190139 (x : ℝ) (hx : x^2 - 5 * x + 7 > 0) :
    Real.logb 0.3 (x^2 - 5 * x + 7) > 0 ↔ 2 < x ∧ x < 3 := by
  constructor
  · -- Assume that Real.logb 0.3 (x^2 - 5 * x + 7) > 0, prove that 2 < x ∧ x < 3.
    intro h
    have h1 : x^2 - 5 * x + 7 < (1 : ℝ) := by
      by_contra h2
      push_neg at h2
      have h2' : Real.logb (0.3 : ℝ) (x^2 - 5 * x + 7) ≤ (0 : ℝ) := by
        have h3 : x^2 - 5 * x + 7 ≥ (1 : ℝ) := h2
        have h4 : Real.logb (0.3 : ℝ) (x^2 - 5 * x + 7) = Real.log ((x^2 - 5 * x + 7)) / Real.log ((0.3 : ℝ)) := by
          field_simp [Real.logb]
        rw [h4]
        have h5 : Real.log ((0.3 : ℝ)) < (0 : ℝ) := by
          have h6 : Real.log ((0.3 : ℝ)) < Real.log ((1 : ℝ)) := by
            apply Real.log_lt_log
            all_goals norm_num
          have h7 : Real.log ((1 : ℝ)) = (0 : ℝ) := Real.log_one
          nlinarith
        have h9 : Real.log ((x^2 - 5 * x + 7)) ≥ (0 : ℝ) := by
          have h10 : x^2 - 5 * x + 7 ≥ (1 : ℝ) := h2
          have h11 : Real.log ((x^2 - 5 * x + 7)) ≥ Real.log ((1 : ℝ)) := by
            apply Real.log_le_log
            all_goals nlinarith
          have h12 : Real.log ((1 : ℝ)) = (0 : ℝ) := Real.log_one
          linarith
        have h13 : Real.log ((x^2 - 5 * x + 7)) / Real.log ((0.3 : ℝ)) ≤ (0 : ℝ) := by
          apply div_nonpos_of_nonneg_of_nonpos
          · linarith
          · linarith
        linarith
      linarith
    have h5 : 2 < x := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3)]
    have h6 : x < 3 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3)]
    exact ⟨h5, h6⟩
  · -- Assume 2 < x ∧ x < 3, prove Real.logb 0.3 (x^2 - 5 * x + 7) > 0.
    rintro ⟨h1, h2⟩
    have h3 : x^2 - 5 * x + 7 < (1 : ℝ) := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3)]
    have h4 : Real.logb 0.3 (x^2 - 5 * x + 7) > (0 : ℝ) := by
      have h5 : Real.logb 0.3 (x^2 - 5 * x + 7) = Real.log ((x^2 - 5 * x + 7)) / Real.log ((0.3 : ℝ)) := by
        field_simp [Real.logb]
      rw [h5]
      have h6 : Real.log ((0.3 : ℝ)) < (0 : ℝ) := by
        have h7 : Real.log ((0.3 : ℝ)) < Real.log ((1 : ℝ)) := by
          apply Real.log_lt_log
          all_goals norm_num
        have h8 : Real.log ((1 : ℝ)) = (0 : ℝ) := Real.log_one
        nlinarith
      have h7 : Real.log ((x^2 - 5 * x + 7)) < (0 : ℝ) := by
        have h8 : x^2 - 5 * x + 7 < (1 : ℝ) := h3
        have h9 : Real.log ((x^2 - 5 * x + 7)) < Real.log ((1 : ℝ)) := by
          apply Real.log_lt_log
          all_goals nlinarith
        have h10 : Real.log ((1 : ℝ)) = (0 : ℝ) := Real.log_one
        linarith
      have h8 : Real.log ((x^2 - 5 * x + 7)) / Real.log ((0.3 : ℝ)) > (0 : ℝ) := by
        apply div_pos_of_neg_of_neg
        · linarith
        · linarith
      linarith
    linarith