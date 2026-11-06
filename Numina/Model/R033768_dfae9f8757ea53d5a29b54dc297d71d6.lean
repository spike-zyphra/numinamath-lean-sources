import Mathlib

theorem algebra_296944 (x : ℝ) :
    (1 + x + x^2) * ∑ i ∈ Finset.range 11, x^i =
    (∑ i ∈ Finset.range 7, x^i)^2 ↔ x = 0 ∨ x = -1 := by 
  constructor
  · -- Assume the equation holds, prove x = 0 or x = -1.
    intro h
    have eq1 : (1 + x + x^2) * ∑ i in Finset.range 11, x^i = (∑ i in Finset.range 7, x^i) ^ 2 := h
    simp [Finset.sum_range_succ] at eq1
    have h2 : x^2 * (x + 1) * (x + 1) = 0 := by
      nlinarith [sq_nonneg (x^5), sq_nonneg (x^4), sq_nonneg (x^3), sq_nonneg (x^2), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x^3 - x^2), sq_nonneg (x^2 - x), sq_nonneg (x^5 - x^2), sq_nonneg (x^4 - x^2)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    cases' (mul_eq_zero.mp h3) with h5 h6
    · -- Case x^2 = 0, so x = 0.
      left
      nlinarith
    · -- Case x + 1 = 0, so x = -1.
      right
      nlinarith
    · -- Case x + 1 = 0, so x = -1.
      right
      nlinarith
  · -- Show the equation holds if x = 0 or x = -1.
    rintro (h | h)
    · -- Case x = 0.
      rw [h]
      norm_num [Finset.sum_range_succ]
    · -- Case x = -1.
      rw [h]
      norm_num [Finset.sum_range_succ]