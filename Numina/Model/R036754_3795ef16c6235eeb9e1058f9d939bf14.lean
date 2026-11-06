import Mathlib

open Real

theorem algebra_2463 {x : ℝ} (hx : x ≠ 1) :
    abs (sqrt (x - 1) - 1) + abs (sqrt (x - 1) + 1) = 1 / (x - 1) ↔ x = 3 / 2 := by
  constructor
  · -- Forward: if the equation is satisfied, then x = 3/2
    intro h
    have h1 : x - 1 > 0 := by
      by_contra h2
      push_neg at h2
      have h1 : sqrt (x - 1) = 0 := by
        rw [Real.sqrt_eq_zero']
        linarith
        all_goals linarith
      have h2 : abs (sqrt (x - 1) - 1) + abs (sqrt (x - 1) + 1) = 2 := by
        rw [h1]
        norm_num [abs]
      rw [h2] at h
      by_cases h4 : x - 1 = 0
      · -- x - 1 = 0
        have h4' : x = 1 := by linarith
        contradiction
      · -- x - 1 ≠ 0
        field_simp [h4] at h
        nlinarith [Real.sqrt_nonneg (x - 1), h1]
    by_cases h3 : sqrt (x - 1) ≥ 1
    · -- Case 1: sqrt (x - 1) ≥ 1
      have h4 : x - 1 ≥ 1 := by
        by_contra h4
        push_neg at h4
        have h5 : sqrt (x - 1) < 1 := by
          have h6 : sqrt (x - 1) < Real.sqrt (1 : ℝ) := by
            apply Real.sqrt_lt_sqrt
            all_goals linarith
          have h7 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
          nlinarith [h6, h7]
        linarith [h3, h5]
      have h5 : abs (sqrt (x - 1) - 1) = sqrt (x - 1) - 1 := by
        rw [abs_of_nonneg]
        linarith [h3]
      have h6 : abs (sqrt (x - 1) + 1) = sqrt (x - 1) + 1 := by
        have h7 : sqrt (x - 1) + 1 ≥ 0 := by
          linarith [Real.sqrt_nonneg (x - 1)]
        rw [abs_of_nonneg h7]
      rw [h5, h6] at h
      have h7 : 2 * sqrt (x - 1) * (x - 1) = 1 := by
        field_simp [(show x - 1 ≠ 0 by
          by_contra h4
          have h4 : x - 1 = 0 := by linarith
          nlinarith
        )] at h ⊢
        nlinarith [h]
      nlinarith [sq_nonneg (sqrt (x - 1) ^ 2 - 1), sq_nonneg (x - 1 - 1),
                Real.sq_sqrt (show 0 ≤ x - 1 by linarith),
                Real.sqrt_nonneg (x - 1)]
    · -- Case 2: sqrt (x - 1) < 1
      have h6 : x - 1 < 1 := by
        by_contra h6
        push_neg at h6
        have h5 : sqrt (x - 1) ≥ 1 := by
          have h6' : sqrt (x - 1) ≥ Real.sqrt (1 : ℝ) := by
            apply Real.sqrt_le_sqrt
            all_goals linarith
          have h7 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
          nlinarith [h6', h7]
        linarith [h5, h3]
      have h5 : abs (sqrt (x - 1) - 1) = 1 - sqrt (x - 1) := by
        have h6 : sqrt (x - 1) - 1 ≤ 0 := by
          linarith [h3, Real.sqrt_nonneg (x - 1)]
        rw [abs_of_nonpos h6]
        all_goals linarith
        all_goals linarith
      have h7 : abs (sqrt (x - 1) + 1) = sqrt (x - 1) + 1 := by
        have h8 : sqrt (x - 1) + 1 ≥ 0 := by
          linarith [Real.sqrt_nonneg (x - 1)]
        rw [abs_of_nonneg h8]
      have h8 : abs (sqrt (x - 1) - 1) + abs (sqrt (x - 1) + 1) = 2 := by
        rw [h5, h7]
        all_goals linarith
      rw [h8] at h
      have h4' : x - 1 = 1 / 2 := by
        field_simp [(show x - 1 ≠ 0 by
          by_contra h4
          have h4 : x - 1 = 0 := by linarith
          nlinarith
        )] at h ⊢
        nlinarith [h]
      linarith [h4']
  · -- Backward: if x = 3/2, then the equation is satisfied
    intro h
    rw [h]
    have h1 : (3 / 2 : ℝ) - 1 = (1 / 2 : ℝ) := by norm_num
    have h2 : sqrt ((3 / 2 : ℝ) - 1) = Real.sqrt (1 / 2 : ℝ) := by
      rw [h1]
    have h3 : abs (sqrt ((3 / 2 : ℝ) - 1) - 1) + abs (sqrt ((3 / 2 : ℝ) - 1) + 1) = (2 : ℝ) := by
      rw [h2]
      have h4 : Real.sqrt (1 / 2 : ℝ) < (1 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (1 / 2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)]
      have h5 : abs (Real.sqrt (1 / 2 : ℝ) - 1) = 1 - Real.sqrt (1 / 2 : ℝ) := by
        have h6 : Real.sqrt (1 / 2 : ℝ) - 1 ≤ 0 := by
          linarith [h4]
        rw [abs_of_nonpos h6]
        all_goals linarith
      have h7 : abs (Real.sqrt (1 / 2 : ℝ) + 1) = Real.sqrt (1 / 2 : ℝ) + 1 := by
        have h8 : Real.sqrt (1 / 2 : ℝ) + 1 ≥ 0 := by
          linarith [Real.sqrt_nonneg (1 / 2 : ℝ)]
        rw [abs_of_nonneg h8]
      rw [h5, h7]
      linarith
    have h4 : (1 / ((3 / 2 : ℝ) - 1) : ℝ) = (2 : ℝ) := by
      rw [show (3 / 2 : ℝ) - 1 = (1 / 2 : ℝ) by norm_num]
      norm_num
    rw [h3, h4]
    all_goals norm_num