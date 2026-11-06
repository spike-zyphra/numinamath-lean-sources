import Mathlib

theorem algebra_186869 (x : ℝ) :
    Real.sqrt (x^2 + 32) - 2 * (x^2 + 32) ^ ((1 : ℝ) / 4) = 3 ↔ x = -7 ∨ x = 7 := by
  constructor
  · -- Forward: If the equation holds, then x is ±7
    intro h_eq
    have h1 : (Real.sqrt (x ^ 2 + 32)) = ((x ^ 2 + 32) ^ ((1 : ℝ) / 4)) ^ 2 := by
      have h2 : ((x ^ 2 + 32) ^ ((1 : ℝ) / 4)) ^ 2 = (x ^ 2 + 32) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals linarith [show 0 ≤ x ^ 2 + 32 by nlinarith]
      rw [h2]
      have h3 : Real.sqrt (x ^ 2 + 32) = (x ^ 2 + 32) ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
      rw [h3]
    rw [h1] at h_eq
    have h2 : ((x ^ 2 + 32 : ℝ) ^ ((1 : ℝ) / 4 : ℝ)) ^ 2 - 2 * ((x ^ 2 + 32 : ℝ) ^ ((1 : ℝ) / 4 : ℝ)) - 3 = 0 := by
      nlinarith [h_eq]
    have h3 : ((x ^ 2 + 32 : ℝ) ^ ((1 : ℝ) / 4 : ℝ)) ^ 2 - 2 * ((x ^ 2 + 32 : ℝ) ^ ((1 : ℝ) / 4 : ℝ)) - 3 = ((x ^ 2 + 32 : ℝ) ^ ((1 : ℝ) / 4 : ℝ) - 3) * ((x ^ 2 + 32 : ℝ) ^ ((1 : ℝ) / 4 : ℝ) + 1) := by
      ring
    rw [h3] at h2
    cases' (mul_eq_zero.1 h2) with h4 h5
    · -- Case fourth root(x^2+32) - 3 = 0
      have h4' : (x ^ 2 + 32 : ℝ) ^ ((1 : ℝ) / 4 : ℝ) = 3 := by linarith
      have h6 : ((x ^ 2 + 32 : ℝ) ^ ((1 : ℝ) / 4 : ℝ)) ^ 4 = (3 : ℝ) ^ 4 := by
        rw [h4']
      have h7 : ((x ^ 2 + 32 : ℝ) ^ ((1 : ℝ) / 4 : ℝ)) ^ 4 = (x ^ 2 + 32 : ℝ) := by
        have h8 : ((x ^ 2 + 32 : ℝ) ^ ((1 : ℝ) / 4 : ℝ)) ^ 4 = (x ^ 2 + 32 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals linarith [show 0 ≤ x ^ 2 + 32 by nlinarith]
        exact h8
      rw [h7] at h6
      have h7 : (x ^ 2 + 32 : ℝ) = (81 : ℝ) := by
        nlinarith [h6]
      have h8 : x ^ 2 = 49 := by
        linarith
      have h9 : x = 7 ∨ x = -7 := by
        have h8' : x ^ 2 - 49 = 0 := by
          linarith
        have h8'' : (x - 7) * (x + 7) = 0 := by
          nlinarith [h8']
        cases' (mul_eq_zero.1 h8'') with h9 h10
        · -- Case x - 7 = 0
          left
          linarith
        · -- Case x + 7 = 0
          right
          linarith
      cases' h9 with h10 h11
      · -- Case x = 7
        right
        linarith
      · -- Case x = -7
        left
        linarith
    · -- Case fourth root(x^2+32) + 1 = 0
      have h6 : (x ^ 2 + 32 : ℝ) ^ ((1 : ℝ) / 4 : ℝ) ≥ 0 := by positivity
      have h7 : (x ^ 2 + 32 : ℝ) ^ ((1 : ℝ) / 4 : ℝ) + 1 = 0 := by linarith [h5]
      nlinarith
  · -- Backward: If x is ±7, then the equation holds
    intro h_eq
    rcases h_eq with (h_eq | h_eq)
    · -- Case x = -7
      rw [show x = (-7 : ℝ) by linarith [h_eq]]
      have h1 : Real.sqrt ((-7 : ℝ) ^ 2 + 32) = (9 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : ((-7 : ℝ) ^ 2 + 32 : ℝ) ^ ((1 : ℝ) / 4) = (3 : ℝ) := by
        have h3 : ((-7 : ℝ) ^ 2 + 32 : ℝ) = (81 : ℝ) := by norm_num
        rw [h3]
        have h4 : (81 : ℝ) ^ ((1 : ℝ) / 4 : ℝ) = (3 : ℝ) := by
          have h5 : (81 : ℝ) ^ ((1 : ℝ) / 4 : ℝ) = (3 : ℝ) := by
            have h6 : (81 : ℝ) = (3 : ℝ) ^ (4 : ℝ) := by norm_num
            rw [h6]
            rw [← Real.rpow_mul]
            norm_num
            all_goals norm_num
          exact h5
        exact h4
      rw [h1, h2]
      norm_num
    · -- Case x = 7
      rw [show x = (7 : ℝ) by linarith [h_eq]]
      have h1 : Real.sqrt ((7 : ℝ) ^ 2 + 32) = (9 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : ((7 : ℝ) ^ 2 + 32 : ℝ) ^ ((1 : ℝ) / 4) = (3 : ℝ) := by
        have h3 : ((7 : ℝ) ^ 2 + 32 : ℝ) = (81 : ℝ) := by norm_num
        rw [h3]
        have h4 : (81 : ℝ) ^ ((1 : ℝ) / 4 : ℝ) = (3 : ℝ) := by
          have h5 : (81 : ℝ) ^ ((1 : ℝ) / 4 : ℝ) = (3 : ℝ) := by
            have h6 : (81 : ℝ) = (3 : ℝ) ^ (4 : ℝ) := by norm_num
            rw [h6]
            rw [← Real.rpow_mul]
            norm_num
            all_goals norm_num
          exact h5
        exact h4
      rw [h1, h2]
      norm_num