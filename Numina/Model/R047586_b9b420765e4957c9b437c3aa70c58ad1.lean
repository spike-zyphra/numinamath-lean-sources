import Mathlib

theorem algebra_20432 : {x : ℝ | (2 * x + 10) * (x + 3) < (3 * x + 9) * (x + 8)} = Set.Iio (-14) ∪ Set.Ioi (-3) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  constructor
  · -- Assume (2 * x + 10) * (x + 3) < (3 * x + 9) * (x + 8)
    intro h
    have h1 : (2 * x + 10) * (x + 3) < (3 * x + 9) * (x + 8) := h
    have h2 : x ^ 2 + 17 * x + 42 > (0 : ℝ) := by
      nlinarith
    by_cases h3 : x < (-14 : ℝ)
    · -- If x < -14, then x ∈ (-∞, -14)
      left
      exact h3
    · -- Now x ≥ -14
      have h4 : x ≥ (-14 : ℝ) := by linarith
      by_cases h5 : x > (-3 : ℝ)
      · -- x > -3, so x ∈ (-3, ∞)
        right
        exact h5
      · -- x ≤ -3
        have h6 : x ≤ (-3 : ℝ) := by linarith
        nlinarith [sq_nonneg (x + 3), sq_nonneg (x + 14), sq_nonneg (x - (-14)), sq_nonneg (x - (-3))]
  · -- Assume x ∈ (-∞, -14) ∪ (-3, ∞)
    rintro (h | h)
    · -- Case x < -14
      have h1 : x < (-14 : ℝ) := by linarith
      have h3 : (2 * x + 10) * (x + 3) < (3 * x + 9) * (x + 8) := by
        nlinarith [sq_nonneg (x + 3), sq_nonneg (x + 14), sq_nonneg (x - (-14)), sq_nonneg (x - (-3))]
      exact h3
    · -- Case x > -3
      have h2 : x > (-3 : ℝ) := by linarith
      have h4 : (2 * x + 10) * (x + 3) < (3 * x + 9) * (x + 8) := by
        nlinarith [sq_nonneg (x + 3), sq_nonneg (x + 14), sq_nonneg (x - (-14)), sq_nonneg (x - (-3))]
      exact h4