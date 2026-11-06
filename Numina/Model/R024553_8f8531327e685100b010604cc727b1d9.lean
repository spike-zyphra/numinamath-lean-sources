import Mathlib

theorem inequalities_88265 (a b c : ℝ) :
    min (min ((a - b)^2) ((b - c)^2)) ((c - a)^2) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 2 := by
  by_cases h1 : (a - b) ^ 2 ≤ (b - c) ^ 2
  · -- Case where (a - b)^2 ≤ (b - c)^2
    have h2 : min ((a - b) ^ 2) ((b - c) ^ 2) = (a - b) ^ 2 := by
      apply min_eq_left
      linarith
    rw [h2]
    by_cases h3 : (a - b) ^ 2 ≤ (c - a) ^ 2
    · -- Case where (a - b)^2 ≤ (c - a)^2
      have h4 : min ((a - b) ^ 2) ((c - a) ^ 2) = (a - b) ^ 2 := by
        apply min_eq_left
        linarith
      rw [h4]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b - c), sq_nonneg (a - b - c), sq_nonneg (a + c - 2 * b), sq_nonneg (a - c + 2 * b)]
    · -- Case where (c - a)^2 < (a - b)^2
      have h4 : min ((a - b) ^ 2) ((c - a) ^ 2) = (c - a) ^ 2 := by
        apply min_eq_right
        nlinarith
      rw [h4]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b - c), sq_nonneg (a - b - c), sq_nonneg (a + c - 2 * b), sq_nonneg (a - c + 2 * b)]
  · -- Case where (b - c)^2 < (a - b)^2
    have h2 : min ((a - b) ^ 2) ((b - c) ^ 2) = (b - c) ^ 2 := by
      apply min_eq_right
      linarith
    rw [h2]
    by_cases h3 : (b - c) ^ 2 ≤ (c - a) ^ 2
    · -- Case where (b - c)^2 ≤ (c - a)^2
      have h4 : min ((b - c) ^ 2) ((c - a) ^ 2) = (b - c) ^ 2 := by
        apply min_eq_left
        linarith
      rw [h4]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b - c), sq_nonneg (a - b - c), sq_nonneg (a + c - 2 * b), sq_nonneg (a - c + 2 * b)]
    · -- Case where (c - a)^2 < (b - c)^2
      have h4 : min ((b - c) ^ 2) ((c - a) ^ 2) = (c - a) ^ 2 := by
        apply min_eq_right
        nlinarith
      rw [h4]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b - c), sq_nonneg (a - b - c), sq_nonneg (a + c - 2 * b), sq_nonneg (a - c + 2 * b)]