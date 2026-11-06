import Mathlib

open BigOperators Real Set

theorem algebra_134188 {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
  (hxy : x + 2 * y = 1 / 2) :
  IsGreatest {u | ∃ x y : ℝ, 0 < x ∧ 0 ≤ y ∧ x + 2 * y = 1 / 2 ∧ u = logb 0.75 (8 * x * y + 4 * y ^ 2 + 1)} 0 ∧
  IsLeast {u | ∃ x y : ℝ, 0 < x ∧ 0 ≤ y ∧ x + 2 * y = 1 / 2 ∧ u = logb 0.75 (8 * x * y + 4 * y ^ 2 + 1)} (-1) := by
  constructor
  · -- Show 0 is the greatest
    constructor
    · -- Show 0 is in the set
      use 1 / 2, (0 : ℝ)
      constructor
      · -- Show 0 < 1/2
        norm_num
      constructor
      · -- Show 0 ≤ (0 : ℝ)
        norm_num
      constructor
      · -- Show 1/2 + 2*0 = 1/2
        norm_num
      · -- Show 0 = logb 0.75 (8 * (1/2) * 0 + 4 * 0 ^ 2 + 1)
        have h9 : logb (0.75 : ℝ) (8 * (1/2 : ℝ) * (0 : ℝ) + 4 * (0 : ℝ) ^ 2 + 1) = (0 : ℝ) := by
          rw [show 8 * (1/2 : ℝ) * (0 : ℝ) + 4 * (0 : ℝ) ^ 2 + 1 = (1 : ℝ) by norm_num]
          rw [Real.logb_one]
        linarith
    · -- Show 0 is greatest
      intro u hu
      rcases hu with ⟨x, y, hx, hy, hxy, heq⟩
      have h1 : 8 * x * y + 4 * y ^ 2 + 1 ≥ (1 : ℝ) := by
        nlinarith [sq_nonneg (y - x / 2), sq_nonneg (y - x), sq_nonneg (y - 1 / 6), sq_nonneg (x - 1 / 2), sq_nonneg (y - 0), sq_nonneg (y - (1 / 4)), mul_pos hx (show 0 < x by linarith)]
      have h13 : logb (0.75 : ℝ) (8 * x * y + 4 * y ^ 2 + 1) ≤ (0 : ℝ) := by
        have h5 : logb (0.75 : ℝ) (8 * x * y + 4 * y ^ 2 + 1) ≤ logb (0.75 : ℝ) (1 : ℝ) := by
          have h6 : logb (0.75 : ℝ) (8 * x * y + 4 * y ^ 2 + 1) = (Real.log (8 * x * y + 4 * y ^ 2 + 1) ) / Real.log (0.75 : ℝ) := by field_simp [logb]
          have h8 : logb (0.75 : ℝ) (1 : ℝ) = (Real.log (1 : ℝ) ) / Real.log (0.75 : ℝ) := by field_simp [logb]
          rw [h6, h8]
          have h13 : Real.log (0.75 : ℝ) < 0 := by
            have h14 : Real.log (0.75 : ℝ) < Real.log (1 : ℝ) := by
              apply Real.log_lt_log
              all_goals norm_num
            have h15 : Real.log (1 : ℝ) = 0 := Real.log_one
            nlinarith
          have h9 : Real.log (8 * x * y + 4 * y ^ 2 + 1) ≥ (0 : ℝ) := by
            have h10 : 8 * x * y + 4 * y ^ 2 + 1 ≥ (1 : ℝ) := h1
            have h11 : Real.log (8 * x * y + 4 * y ^ 2 + 1) ≥ Real.log (1 : ℝ) := by
              apply Real.log_le_log
              all_goals
                nlinarith
            have h12 : Real.log (1 : ℝ) = (0 : ℝ) := Real.log_one
            nlinarith
          have h14 : (Real.log (8 * x * y + 4 * y ^ 2 + 1) ) / Real.log (0.75 : ℝ) ≤ (0 : ℝ) := by
            apply (div_nonpos_iff).mpr
            left
            constructor
            · linarith
            · nlinarith
          have h15 : (Real.log (1 : ℝ) ) / Real.log (0.75 : ℝ) = (0 : ℝ) := by
            have h16 : Real.log (1 : ℝ) = (0 : ℝ) := Real.log_one
            rw [h16]
            norm_num
          nlinarith
        have h7 : logb (0.75 : ℝ) (1 : ℝ) = (0 : ℝ) := by
          rw [Real.logb_one]
        linarith
      have h16 : u ≤ (0 : ℝ) := by
        nlinarith [heq, h13]
      linarith
  · -- Show -1 is the least
    constructor
    · -- Show -1 is in the set
      use 1 / 6, 1 / 6
      constructor
      · -- Show 0 < 1/6
        norm_num
      constructor
      · -- Show 0 ≤ 1/6
        norm_num
      constructor
      · -- Show 1/6 + 2*(1/6) = 1/2
        norm_num
      · -- Show -1 = logb 0.75 (8 * (1/6) * (1/6) + 4 * (1/6) ^ 2 + 1)
        have h12 : logb (0.75 : ℝ) (8 * (1/6 : ℝ) * (1/6 : ℝ) + 4 * (1/6 : ℝ) ^ 2 + 1) = -1 := by
          have h13 : 8 * (1/6 : ℝ) * (1/6 : ℝ) + 4 * (1/6 : ℝ) ^ 2 + 1 = (4 / 3 : ℝ) := by norm_num
          rw [h13]
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        linarith
    · -- Show -1 is the least
      intro u hu
      rcases hu with ⟨x, y, hx, hy, hxy, heq⟩
      have h1 : 8 * x * y + 4 * y ^ 2 + 1 ≤ (4 / 3 : ℝ) := by
        have h2 : x = 1 / 2 - 2 * y := by linarith
        rw [h2] at *
        nlinarith [sq_nonneg (y - 1 / 6), sq_nonneg (y - 1 / 4), sq_nonneg (y - 0), sq_nonneg (y - 1 / 4), sq_nonneg (y - 1 / 6), mul_pos hx (show 0 < x by linarith)]
      have h13 : logb (0.75 : ℝ) (8 * x * y + 4 * y ^ 2 + 1) ≥ (-1 : ℝ) := by
        have h14 : logb (0.75 : ℝ) (8 * x * y + 4 * y ^ 2 + 1) ≥ logb (0.75 : ℝ) (4 / 3 : ℝ) := by
          have h9 : 8 * x * y + 4 * y ^ 2 + 1 ≤ (4 / 3 : ℝ) := h1
          have h10 : 0 < (4 / 3 : ℝ) := by norm_num
          have h11 : 0 < 8 * x * y + 4 * y ^ 2 + 1 := by
            nlinarith [sq_nonneg (y - x / 2), sq_nonneg (y - x), sq_nonneg (y - 1 / 6), sq_nonneg (x - 1 / 2), sq_nonneg (y - 0), sq_nonneg (y - (1 / 4)), mul_pos hx (show 0 < x by linarith)]
          have h12 : logb (0.75 : ℝ) (8 * x * y + 4 * y ^ 2 + 1) ≥ logb (0.75 : ℝ) (4 / 3 : ℝ) := by
            have h13 : logb (0.75 : ℝ) (8 * x * y + 4 * y ^ 2 + 1) = (Real.log (8 * x * y + 4 * y ^ 2 + 1) ) / Real.log (0.75 : ℝ) := by field_simp [logb]
            have h14 : logb (0.75 : ℝ) (4 / 3 : ℝ) = (Real.log (4 / 3 : ℝ) ) / Real.log (0.75 : ℝ) := by field_simp [logb]
            rw [h13, h14]
            have h15 : Real.log (0.75 : ℝ) < 0 := by
              have h16 : Real.log (0.75 : ℝ) < Real.log (1 : ℝ) := by
                apply Real.log_lt_log
                all_goals norm_num
              have h17 : Real.log (1 : ℝ) = 0 := Real.log_one
              nlinarith
            have h18 : Real.log (8 * x * y + 4 * y ^ 2 + 1) ≤ Real.log (4 / 3 : ℝ) := by
              have h19 : 8 * x * y + 4 * y ^ 2 + 1 ≤ (4 / 3 : ℝ) := h1
              have h20 : 8 * x * y + 4 * y ^ 2 + 1 > 0 := by
                nlinarith
              have h21 : (4 / 3 : ℝ) > 0 := by norm_num
              have h22 : Real.log (8 * x * y + 4 * y ^ 2 + 1) ≤ Real.log (4 / 3 : ℝ) := by
                apply Real.log_le_log
                all_goals nlinarith
              linarith
            apply (div_le_div_right_of_neg (by linarith)).mpr
            nlinarith
          linarith
        have h15 : logb (0.75 : ℝ) (4 / 3 : ℝ) = -1 := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        linarith
      have h16 : u ≥ (-1 : ℝ) := by
        nlinarith [heq, h13]
      linarith