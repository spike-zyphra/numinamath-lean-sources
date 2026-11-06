import Mathlib

theorem inequalities_219820 (x : ℝ) :
  abs (abs (abs (x - 9) - x) + 2 * x) ≤ 2009 ↔ x ≤ 1000 := by
  constructor
  · -- Assume abs (abs (abs (x - 9) - x) + 2 * x) ≤ 2009, prove x ≤ 1000
    intro h
    by_contra h3
    push_neg at h3
    have h3' : x - 9 > 0 := by linarith
    have h4 : abs (x - 9) = x - 9 := by
      rw [abs_of_pos]
      linarith
    have h5 : abs (abs (x - 9) - x) = 9 := by
      rw [h4]
      have h7 : (x - 9 : ℝ) - x = -9 := by linarith
      rw [h7]
      norm_num [abs_of_nonneg]
    have h8 : abs (abs (abs (x - 9) - x) + 2 * x) = 9 + 2 * x := by
      rw [h5]
      have h9 : (9 + (2 * x : ℝ) ) ≥ 0 := by
        linarith
      rw [abs_of_nonneg h9]
    nlinarith [abs_nonneg (abs (abs (x - 9) - x) + 2 * x), abs_nonneg (abs (x - 9) - x), abs_nonneg (x - 9)]
  · -- Assume x ≤ 1000, prove abs (abs (abs (x - 9) - x) + 2 * x) ≤ 2009
    intro h
    by_cases h2 : x ≤ 9
    · -- x ≤ 9
      have h3 : abs (x - 9) = 9 - x := by
        rw [abs_of_nonpos]
        linarith
        all_goals linarith
      by_cases h4 : x ≤ 4.5
      · -- x ≤ 4.5
        have h5 : abs (abs (x - 9) - x) = 9 - 2 * x := by
          rw [h3]
          rw [abs_of_nonneg]
          linarith
          all_goals linarith
        have h6 : abs (abs (abs (x - 9) - x) + 2 * x) = abs ((9 - 2 * x) + 2 * x) := by
          rw [h5]
        rw [h6]
        have h7 : (9 - 2 * x : ℝ) + 2 * x = 9 := by
          linarith
        rw [h7]
        norm_num [abs_le]
      · -- x > 4.5
        have h4' : x > 4.5 := by linarith
        have h5 : abs (abs (x - 9) - x) = 2 * x - 9 := by
          rw [h3]
          rw [abs_of_neg]
          linarith
          all_goals linarith
        have h6 : abs (abs (abs (x - 9) - x) + 2 * x) = abs ((2 * x - 9) + 2 * x) := by
          rw [h5]
        rw [h6]
        have h7 : (2 * x - 9 : ℝ) + 2 * x = 4 * x - 9 := by
          linarith
        rw [h7]
        have h8 : abs (4 * x - 9) ≤ 2009 := by
          rw [abs_le]
          constructor
          · -- Prove -2009 ≤ 4 * x - 9
            nlinarith
          · -- Prove 4 * x - 9 ≤ 2009
            nlinarith
        exact h8
    · -- x > 9
      have h2' : x > 9 := by linarith
      have h3 : abs (x - 9) = x - 9 := by
        rw [abs_of_pos]
        linarith
      have h5 : abs (abs (x - 9) - x) = 9 := by
        rw [h3]
        have h7 : (x - 9 : ℝ) - x = -9 := by linarith
        rw [h7]
        norm_num [abs_of_nonneg]
      have h8 : abs (abs (abs (x - 9) - x) + 2 * x) = abs ((9 : ℝ) + 2 * x) := by
        rw [h5]
      have h9 : abs ((9 : ℝ) + 2 * x) ≤ 2009 := by
        rw [abs_le]
        constructor
        · -- Prove -2009 ≤ 9 + 2 * x
          nlinarith
        · -- Prove 9 + 2 * x ≤ 2009
          nlinarith
      rw [h8]
      exact h9