import Mathlib

/-The integer solutions of the equation (x ^ 2 + x - 1) ^ (x + 98) = 1 are
() in number -/

theorem algebra_317265 : {x : ℤ | (x ^ 2 + x - 1) ^ (x + 98) = (1: ℚ)}.encard = 4 := by

  have h_eq: {x : ℤ | (x ^ 2 + x - 1) ^ (x + 98) = (1: ℚ)} = {-98, 1, -2, 0}:= by
    ext x
    constructor
    -- the forward direction
    .
      intro h
      simp at h
      simp
      by_cases l: 0 ≤ x ^ 2 + x - 1
      .
        by_cases l1: x ^ 2 + x - 1 = 1
        .
          replace l1: x ^ 2 + x - 2 = 0:= by omega
          rw [show x ^ 2 + x - 2 = (x - 1) * (x + 2) by ring] at l1
          simp at l1
          omega
        .
          rw [zpow_eq_one_iff_right₀] at h
          left
          linarith
          simp
          norm_cast
          linarith
          norm_cast
      .
        simp at l
        rw [show (x: ℚ) ^ 2 + ↑x - 1 = (-1) * (- (↑x ^ 2 + ↑x - 1)) by ring] at h
        rw [Commute.mul_zpow] at h
        by_cases o: Even (x + 98)
        .
          by_contra! y
          have s: (-1: ℚ) ^ (x + 98) = (1: ℚ) := by
            apply Even.neg_one_zpow
            exact o
          simp [s] at h
          rw [zpow_eq_one_iff_right₀] at h
          omega
          norm_cast
          linarith
          norm_cast
          by_contra! o
          simp at o
          rw [show x ^ 2 + x = x * (x + 1) by ring] at o
          simp at o
          rcases o with o | o
          .
            simp [o] at y
          .
            replace o: x = -1 := by omega
            simp [o] at s
            norm_num at s
        .
          simp at o
          have t: Even (x + 97) := by
            rw [show x + 97 = (x + 98) - 1 by ring]
            rw [Int.even_sub' ]
            simp [o]
          rw [show x + 98 = (x + 97) + 1 by ring] at h
          rw [zpow_add_one₀] at h
          have s: (-1: ℚ) ^ (x + 97) = (1: ℚ) := by
            apply Even.neg_one_zpow
            exact t
          simp [s] at h
          replace h: (1 - (↑x ^ 2 + ↑x)) ^ (x + 97 + 1) = (-1: ℚ) := by linarith
          rw [zpow_add_one₀] at h
          have r1: (0: ℚ) ≤ (1 - (↑x ^ 2 + ↑x)) ^ (x + 97) := by
             apply Even.zpow_nonneg
             exact t
          have r2: (0: ℚ) ≤ 1 - (↑x ^ 2 + ↑x) := by norm_cast; linarith
          nlinarith
          norm_cast
          linarith
          norm_num
        simp

    -- the backward direction
    .
      intro h
      simp at h
      rcases h with h | h | h | h
      all_goals simp [h]
      all_goals norm_num


-- finally, we can compute the cardinality of the set
  rw [h_eq]
  simp [Set.encard]