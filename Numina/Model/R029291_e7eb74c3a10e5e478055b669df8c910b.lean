import Mathlib

theorem inequalities_319945 (x : ℝ) (h1: x+1 ≠ 0) (h2: 2*x+1 ≠ 0) (h3: 3*x+1 ≠ 0) :
    (x / (x + 1) + 2 * x / ((x + 1) * (2 * x + 1)) + 3 * x / ((x + 1) * (2 * x + 1) * (3 * x + 1))) > 1 ↔
    x < -1 ∨ (-1 / 2 < x ∧ x < -1 / 3) := by 
  constructor
  · -- First, we show that if the inequality holds, then the conclusion is true.
    intro h
    have h4 : x / (x + 1) + 2 * x / ((x + 1) * (2 * x + 1)) + 3 * x / ((x + 1) * (2 * x + 1) * (3 * x + 1)) - 1 > 0 := by linarith 
    have h5 : x / (x + 1) + 2 * x / ((x + 1) * (2 * x + 1)) + 3 * x / ((x + 1) * (2 * x + 1) * (3 * x + 1)) - 1 = (-1) / ((x + 1) * (2 * x + 1) * (3 * x + 1)) := by 
      field_simp [(show x + 1 ≠ 0 by assumption), (show 2 * x + 1 ≠ 0 by assumption), (show 3 * x + 1 ≠ 0 by assumption)]
      ring
    have h6 : (-1 : ℝ) / ((x + 1) * (2 * x + 1) * (3 * x + 1)) > 0 := by 
      linarith [h4, h5]
    have h7 : (x + 1) * (2 * x + 1) * (3 * x + 1) < 0 := by
      by_contra h
      push_neg at h
      have h8 : (-1 : ℝ) / ((x + 1) * (2 * x + 1) * (3 * x + 1)) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · norm_num
        all_goals
          nlinarith [sq_nonneg ((x + 1) * (2 * x + 1)), sq_nonneg ((x + 1) * (3 * x + 1)), sq_nonneg ((2 * x + 1) * (3 * x + 1))]
      linarith 
    by_cases h8 : x < -1
    · -- Case x < -1, prove first disjunction.
      left 
      exact h8 
    · -- Case x ≥ -1, need to prove second disjunction.
      have h9 : x ≥ -1 := by linarith
      have h7 : (x + 1) * (2 * x + 1) * (3 * x + 1) < 0 := h7
      have h11 : x + 1 > 0 := by 
        by_contra h 
        push_neg at h 
        have h12 : x + 1 = 0 := by
          nlinarith 
        contradiction 
      have h12 : (2 * x + 1) * (3 * x + 1) < 0 := by
        nlinarith [h11, h7, mul_pos (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) < 1 by norm_num), h9] 
      have h13 : -1 / 2 < x := by 
        nlinarith [h12] 
      have h14 : x < -1 / 3 := by 
        nlinarith [h12] 
      right 
      constructor 
      · -- Show -1/2 < x 
        linarith 
      · -- Show x < -1/3 
        linarith 
  · -- Now prove the reverse direction.
    intro h 
    cases h with 
    | inl h11 => 
      have h4 : (x + 1) * (2 * x + 1) * (3 * x + 1) < 0 := by 
        have h6 : x + 1 < 0 := by linarith 
        have h7 : 2 * x + 1 < 0 := by linarith 
        have h8 : 3 * x + 1 < 0 := by linarith 
        have h9 : (x + 1) * (2 * x + 1) * (3 * x + 1) < 0 := by 
          have h10 : (x + 1) * (2 * x + 1) > 0 := by nlinarith 
          nlinarith 
        linarith 
      have h5 : (x / (x + 1) + 2 * x / ((x + 1) * (2 * x + 1)) + 3 * x / ((x + 1) * (2 * x + 1) * (3 * x + 1))) - 1 = (-1) / ((x + 1) * (2 * x + 1) * (3 * x + 1)) := by 
        field_simp [(show x + 1 ≠ 0 by assumption), (show 2 * x + 1 ≠ 0 by assumption), (show 3 * x + 1 ≠ 0 by assumption)]
        ring 
      have h6 : (-1 : ℝ) / ((x + 1) * (2 * x + 1) * (3 * x + 1)) > 0 := by 
        apply div_pos_of_neg_of_neg 
        · norm_num 
        all_goals 
          nlinarith 
      linarith [h5, h6] 
    | inr h11 => 
      have h7 : -1 / 2 < x := by linarith [h11.1] 
      have h8 : x < -1 / 3 := by linarith [h11.2] 
      have h4 : (x + 1) * (2 * x + 1) * (3 * x + 1) < 0 := by 
        have h6 : x + 1 > 0 := by linarith 
        have h7 : 2 * x + 1 > 0 := by linarith 
        have h8 : 3 * x + 1 < 0 := by linarith 
        have h9 : (x + 1) * (2 * x + 1) * (3 * x + 1) < 0 := by 
          have h10 : (x + 1) * (2 * x + 1) > 0 := by nlinarith 
          nlinarith 
        linarith 
      have h5 : (x / (x + 1) + 2 * x / ((x + 1) * (2 * x + 1)) + 3 * x / ((x + 1) * (2 * x + 1) * (3 * x + 1))) - 1 = (-1) / ((x + 1) * (2 * x + 1) * (3 * x + 1)) := by 
        field_simp [(show x + 1 ≠ 0 by assumption), (show 2 * x + 1 ≠ 0 by assumption), (show 3 * x + 1 ≠ 0 by assumption)]
        ring 
      have h6 : (-1 : ℝ) / ((x + 1) * (2 * x + 1) * (3 * x + 1)) > 0 := by 
        apply div_pos_of_neg_of_neg 
        · norm_num 
        all_goals 
          nlinarith 
      linarith [h5, h6]