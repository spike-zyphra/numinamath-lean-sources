import Mathlib

open Real Set

theorem algebra_326392 {x : ℝ} (hx : x ≥ -2) :
    sqrt (x + 3 - 2 * sqrt (x + 2)) + sqrt (x + 6 - 4 * sqrt (x + 2)) = 1 ↔
    -1 ≤ x ∧ x ≤ 2 := by
  constructor
  · -- Forward implication: equation → interval
    intro h_eq
    have h1 : x ≥ -2 := hx
    have h2 : x + 3 - 2 * sqrt (x + 2) = (sqrt (x + 2) - 1) ^ 2 := by
      have h3 : (sqrt (x + 2)) ^ 2 = x + 2 := by
        rw [Real.sq_sqrt]
        linarith
      nlinarith
    have h4 : x + 6 - 4 * sqrt (x + 2) = (sqrt (x + 2) - 2) ^ 2 := by
      have h3 : (sqrt (x + 2)) ^ 2 = x + 2 := by
        rw [Real.sq_sqrt]
        linarith
      nlinarith
    have h5 : sqrt (x + 3 - 2 * sqrt (x + 2)) = abs (sqrt (x + 2) - 1) := by
      rw [h2]
      have h6 : sqrt ((sqrt (x + 2) - 1) ^ 2) = abs (sqrt (x + 2) - 1) := by
        rw [Real.sqrt_sq_eq_abs]
      rw [h6]
    have h7 : sqrt (x + 6 - 4 * sqrt (x + 2)) = abs (sqrt (x + 2) - 2) := by
      rw [h4]
      have h8 : sqrt ((sqrt (x + 2) - 2) ^ 2) = abs (sqrt (x + 2) - 2) := by
        rw [Real.sqrt_sq_eq_abs]
      rw [h8]
    rw [h5, h7] at h_eq
    by_cases h9 : sqrt (x + 2) ≥ 2
    · -- Case 1: sqrt (x + 2) ≥ 2
      have h10 : abs (sqrt (x + 2) - 1) = sqrt (x + 2) - 1 := by
        have h11 : sqrt (x + 2) - 1 ≥ 0 := by
          nlinarith
        rw [abs_of_nonneg h11]
      have h12 : abs (sqrt (x + 2) - 2) = sqrt (x + 2) - 2 := by
        have h13 : sqrt (x + 2) - 2 ≥ 0 := by
          linarith
        rw [abs_of_nonneg h13]
      rw [h10, h12] at h_eq
      have h11 : sqrt (x + 2) = 2 := by
        nlinarith
      have h12 : x + 2 = 4 := by
        calc
          x + 2 = (sqrt (x + 2)) ^ 2 := by
            rw [Real.sq_sqrt]
            linarith
          _ = (2) ^ 2 := by
            rw [h11]
          _ = (4 : ℝ) := by
            norm_num
      have hx2 : x = 2 := by
        nlinarith
      constructor
      · -- Show -1 ≤ x
        nlinarith
      · -- Show x ≤ 2
        nlinarith
    · -- sqrt (x + 2) < 2
      by_cases h10 : sqrt (x + 2) ≥ 1
      · -- Case 2: 1 ≤ sqrt (x + 2) < 2
        have h11 : abs (sqrt (x + 2) - 1) = sqrt (x + 2) - 1 := by
          have h12 : sqrt (x + 2) - 1 ≥ 0 := by
            linarith
          rw [abs_of_nonneg h12]
        have h12 : abs (sqrt (x + 2) - 2) = 2 - sqrt (x + 2) := by
          have h13 : sqrt (x + 2) - 2 ≤ 0 := by
            nlinarith
          rw [abs_of_nonpos h13]
          all_goals linarith
        rw [h11, h12] at h_eq
        have h14 : 1 ≤ sqrt (x + 2) := by
          linarith
        have h15 : sqrt (x + 2) ≤ (2 : ℝ) := by
          nlinarith
        have hx3 : 1 ≤ (x + 2 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (x + 2 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ x + 2 by linarith)]
        have hx4 : (x + 2 : ℝ) ≤ (4 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (x + 2 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ x + 2 by linarith)]
        constructor
        · -- Show -1 ≤ x
          nlinarith [Real.sqrt_nonneg (x + 2 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ x + 2 by linarith)]
        · -- Show x ≤ 2
          nlinarith [Real.sqrt_nonneg (x + 2 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ x + 2 by linarith)]
      · -- Case 3: sqrt (x + 2) < 1
        have h14 : abs (sqrt (x + 2) - 1) = 1 - sqrt (x + 2) := by
          have h15 : sqrt (x + 2) - 1 ≤ 0 := by
            nlinarith
          rw [abs_of_nonpos h15]
          all_goals linarith
        have h15 : abs (sqrt (x + 2) - 2) = 2 - sqrt (x + 2) := by
          have h16 : sqrt (x + 2) - 2 ≤ 0 := by
            nlinarith
          rw [abs_of_nonpos h16]
          all_goals linarith
        rw [h14, h15] at h_eq
        nlinarith [Real.sqrt_nonneg (x + 2 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ x + 2 by linarith)]
  · -- Backward implication: interval → equation
    rintro ⟨hx1, hx2⟩
    have h1 : x ≥ -2 := by linarith
    have h2 : x + 3 - 2 * sqrt (x + 2) = (sqrt (x + 2) - 1) ^ 2 := by
      have h3 : (sqrt (x + 2)) ^ 2 = x + 2 := by
        rw [Real.sq_sqrt]
        linarith
      nlinarith
    have h4 : x + 6 - 4 * sqrt (x + 2) = (sqrt (x + 2) - 2) ^ 2 := by
      have h3 : (sqrt (x + 2)) ^ 2 = x + 2 := by
        rw [Real.sq_sqrt]
        linarith
      nlinarith
    have h5 : sqrt (x + 3 - 2 * sqrt (x + 2)) = abs (sqrt (x + 2) - 1) := by
      rw [h2]
      have h6 : sqrt ((sqrt (x + 2) - 1) ^ 2) = abs (sqrt (x + 2) - 1) := by
        rw [Real.sqrt_sq_eq_abs]
      rw [h6]
    have h7 : sqrt (x + 6 - 4 * sqrt (x + 2)) = abs (sqrt (x + 2) - 2) := by
      rw [h4]
      have h8 : sqrt ((sqrt (x + 2) - 2) ^ 2) = abs (sqrt (x + 2) - 2) := by
        rw [Real.sqrt_sq_eq_abs]
      rw [h8]
    rw [h5, h7]
    have hs1 : sqrt (x + 2) ≥ 1 := by
      have hs2 : x + 2 ≥ (1 : ℝ) := by
        nlinarith
      have h13 : sqrt (x + 2) ≥ sqrt (1 : ℝ) := by
        apply Real.sqrt_le_sqrt
        all_goals linarith
      have h14 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      nlinarith
      all_goals nlinarith
      all_goals linarith
    have hs2 : sqrt (x + 2) ≤ 2 := by
      have hs3 : x + 2 ≤ (4 : ℝ) := by
        nlinarith
      have h13 : sqrt (x + 2) ≤ sqrt (4 : ℝ) := by
        apply Real.sqrt_le_sqrt
        all_goals linarith
      have h14 : sqrt (4 : ℝ) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      nlinarith
      all_goals nlinarith
      all_goals linarith
    have h15 : abs (sqrt (x + 2) - 1) = sqrt (x + 2) - 1 := by
      have h16 : sqrt (x + 2) - 1 ≥ 0 := by
        nlinarith
      rw [abs_of_nonneg h16]
    have h16 : abs (sqrt (x + 2) - 2) = 2 - sqrt (x + 2) := by
      have h17 : sqrt (x + 2) - 2 ≤ 0 := by
        nlinarith
      rw [abs_of_nonpos h17]
      all_goals linarith
    rw [h15, h16]
    nlinarith