import Mathlib

theorem algebra_138444 (x : ℝ) (hx : x > 0) :
    x^101 + 100^99 = x^99 + 100^101 ↔ x = 100 := by
  constructor
  · -- Assume x^101 + 100^99 = x^99 + 100^101, prove x = 100
    intro h
    have h1 : x ^ 101 + 100 ^ 99 = x ^ 99 + 100 ^ 101 := h
    have h2 : x ^ 101 - x ^ 99 = 100 ^ 101 - 100 ^ 99 := by
      nlinarith
    have h3 : x ^ 101 - x ^ 99 = x ^ 99 * (x ^ 2 - 1) := by
      ring
    have h4 : (100 : ℝ) ^ 101 - (100 : ℝ) ^ 99 = (100 ^ 99) * ((100 : ℝ) ^ 2 - 1) := by
      ring
    rw [h3] at h2
    rw [h4] at h2
    have h5 : x ^ 99 * (x ^ 2 - 1) = (100 ^ 99) * ((100 : ℝ) ^ 2 - 1) := by
      linarith
    by_cases h6 : x < 100
    · -- Case x < 100
      have h7 : x < 100 := h6
      have h8 : (x : ℝ) ^ 99 < (100 : ℝ) ^ 99 := by
        apply pow_lt_pow_left
        all_goals nlinarith
      have h9 : (x : ℝ) ^ 2 < (100 : ℝ) ^ 2 := by
        nlinarith
      have h10 : (x : ℝ) ^ 2 - 1 < (100 : ℝ) ^ 2 - 1 := by
        nlinarith
      have h11 : (x ^ 99 * (x^2 - 1) : ℝ) < (100^99 * ((100 : ℝ) ^ 2 - 1) : ℝ) := by
        nlinarith [mul_pos (show (0 : ℝ) < x by linarith) (show (0 : ℝ) < x ^ 98 by positivity), h8, h10, sq_nonneg (x ^ 2 - 1), sq_nonneg ((100 : ℝ) ^ 2 - 1)]
      linarith [h5, h11]
    · -- Case x >= 100
      by_cases h7 : x > 100
      · -- Case x > 100
        have h8 : (x : ℝ) > 100 := h7
        have h9 : (x : ℝ) ^ 99 > (100 : ℝ) ^ 99 := by
          apply pow_lt_pow_left
          all_goals nlinarith
        have h10 : (x : ℝ) ^ 2 > (100 : ℝ) ^ 2 := by
          nlinarith
        have h11 : (x : ℝ) ^ 2 - 1 > (100 : ℝ) ^ 2 - 1 := by
          nlinarith
        have h12 : (x ^ 99 * (x ^ 2 - 1) : ℝ) > (100 ^ 99 * ((100 : ℝ) ^ 2 - 1) : ℝ) := by
          nlinarith [mul_pos (show (0 : ℝ) < x by linarith) (show (0 : ℝ) < x ^ 98 by positivity), h9, h11, sq_nonneg (x ^ 2 - 1), sq_nonneg ((100 : ℝ) ^ 2 - 1)]
        linarith [h5, h12]
      · -- Case x = 100
        have h8 : x <= 100 := by nlinarith
        have h9 : x >= 100 := by nlinarith
        have h10 : x = 100 := by linarith
        exact h10
  · -- Assume x = 100, prove x^101 + 100^99 = x^99 + 100^101
    intro h
    rw [h]
    all_goals norm_num