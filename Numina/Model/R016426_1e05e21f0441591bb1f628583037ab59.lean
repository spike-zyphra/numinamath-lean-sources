import Mathlib

theorem algebra_180883 (x : ℝ) :
    abs (x + 1) + abs (x - 1) = 2 * x^3 ↔ x = 1 := by
  constructor
  · -- Forward implication: abs (x + 1) + abs (x - 1) = 2 * x^3 → x = 1
    intro h
    by_cases h1 : x ≥ 1
    · -- Case 1: x ≥ 1
      rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), abs_of_nonneg (show x - 1 ≥ 0 by linarith)] at h
      have h2 : x^3 = x := by
        nlinarith
      have h3 : x^3 - x = 0 := by
        linarith
      have h4 : (x - 1) * x * (x + 1) = 0 := by
        ring_nf at h3 ⊢
        linarith
      cases' (mul_eq_zero.mp h4) with h5 h6
      · cases' (mul_eq_zero.mp h5) with h7 h8
        · -- Case 1a: x - 1 = 0, so x = 1
          linarith
        · -- Case 1b: x = 0, which contradicts x ≥ 1
          nlinarith
      · -- Case 2: x + 1 = 0, so x = -1 which contradicts x ≥ 1
        nlinarith
    by_cases h2 : x ≥ -1
    · -- Case 2: -1 ≤ x < 1
      rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), abs_of_nonpos (show x - 1 ≤ 0 by linarith)] at h
      have h3 : x^3 = 1 := by
        nlinarith
      have h4 : x = 1 := by
        have h5 : x^3 - 1 = 0 := by nlinarith
        have h6 : (x - 1) * (x^2 + x + 1) = 0 := by
          ring_nf at h5 ⊢
          linarith
        cases' (mul_eq_zero.mp h6) with h7 h8
        · -- Case where x - 1 = 0, so x = 1.
          linarith
        · -- Case where x^2 + x + 1 = 0, which has no real solutions.
          nlinarith [sq_nonneg (x + 1/2)]
      linarith -- Contradicts x < 1
    · -- Case 3: x < -1
      rw [abs_of_nonpos (show x + 1 ≤ 0 by linarith), abs_of_nonpos (show x - 1 ≤ 0 by linarith)] at h
      nlinarith [sq_nonneg (x^2), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x * (x + 1)), sq_nonneg (x * (x - 1)), sq_nonneg ((x + 1) * (x - 1))]
  · -- Backward implication: x = 1 → abs (x + 1) + abs (x - 1) = 2 * x^3
    rintro h1
    rw [h1]
    norm_num [abs_of_nonneg, abs_of_nonpos]