import Mathlib

theorem algebra_328056 (a b : ℝ) (h : 3 * a ^ 2 - 10 * a * b + 8 * b ^ 2 + 5 * a - 10 * b = 0) :
    9 * a ^ 2 + 72 * b + 2 ≥ -34 := by
  have h1 : (a - 2 * b) * (3 * a - 4 * b + 5) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h1) with h2 h3
  · -- Case where a = 2b
    have ha : a = 2 * b := by linarith
    have h4 : 9 * a ^ 2 + 72 * b + 2 = 36 * (b + 1) ^ 2 - 34 := by
      rw [ha]
      ring
    rw [h4]
    have h5 : 36 * (b + 1) ^ 2 ≥ 0 := by
      apply mul_nonneg
      norm_num
      apply pow_two_nonneg
    linarith [sq_nonneg (b + 1)]
  · -- Case where 3a - 4b + 5 = 0
    have ha : 3 * a = 4 * b - 5 := by linarith [h3]
    have ha' : a = (4 * b - 5) / 3 := by linarith
    have h6 : 9 * a ^ 2 + 72 * b + 2 = 16 * (b + 1) ^ 2 + 11 := by
      rw [ha']
      nlinarith
    rw [h6]
    nlinarith [sq_nonneg (b + 1)]