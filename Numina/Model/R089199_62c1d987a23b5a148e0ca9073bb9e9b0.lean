import Mathlib

theorem algebra_312 {a b : ℝ} (h1 : a^5 - a^4 * b - a^4 + a - b - 1 = 0) (h2 : 2 * a - 3 * b - 1 = 0) : a^5 + b^5 = 33 := by
  have eq1 : b = (2 * a - 1) / 3 := by
    linarith
  rw [eq1] at h1
  have h3 : a^5 - 2 * a^4 + a - 2 = 0 := by
    nlinarith [sq_nonneg (a^2 - a), sq_nonneg (a^2 + a), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (a^4 - 2 * a^3), sq_nonneg (a^4 + 2 * a^3)]
  have h4 : (a - 2) * (a^4 + 1) = 0 := by
    nlinarith [sq_nonneg (a^2 - a), sq_nonneg (a^2 + a), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (a^4 - 2 * a^3), sq_nonneg (a^4 + 2 * a^3)]
  cases' (mul_eq_zero.1 h4) with ha h5
  · -- Case where a - 2 = 0, so a = 2
    have ha2 : a = 2 := by linarith
    have hb1 : b = 1 := by
      rw [ha2] at eq1
      linarith
    rw [ha2, hb1]
    norm_num
  · -- Case where a^4 + 1 = 0, which is impossible
    nlinarith [sq_nonneg (a^2), sq_nonneg (a^4)]