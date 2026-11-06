import Mathlib

theorem algebra_70913 {a b : ℝ}
    (ha : a^3-6*a^2+15*a=9) (hb : b^3-3*b^2+6*b=-1) :
    (a-b)^2014=1 := by
  have h1 : a^3 - 6 * a^2 + 15 * a - 9 = 0 := by linarith
  have h2 : b^3 - 3 * b^2 + 6 * b + 1 = 0 := by linarith
  have h3 : (a - 2) ^ 3 + 3 * (a - 2) + 5 = 0 := by
    nlinarith [sq_nonneg (a - 2), sq_nonneg (a - 3), sq_nonneg (a - 1)]
  have h4 : (b - 1) ^ 3 + 3 * (b - 1) + 5 = 0 := by
    nlinarith [sq_nonneg (b - 1), sq_nonneg (b - 2), sq_nonneg (b)]
  have h5 : a - 2 = b - 1 := by
    have h6 : (a - 2) ^ 3 + 3 * (a - 2) + 5 = 0 := h3
    have h7 : (b - 1) ^ 3 + 3 * (b - 1) + 5 = 0 := h4
    have h8 : (a - 2) ^ 3 + 3 * (a - 2) = (b - 1) ^ 3 + 3 * (b - 1) := by linarith
    have h9 : a - 2 = b - 1 := by
      have h10 : (a - 2 - (b - 1)) * ((a - 2) ^ 2 + (a - 2) * (b - 1) + (b - 1) ^ 2 + 3) = 0 := by
        ring_nf at h8 ⊢
        nlinarith
      cases' (mul_eq_zero.1 h10) with h12 h13
      · -- Case where the first factor is zero, i.e., a - 2 = b - 1
        linarith
      · -- Case where the second factor is zero
        have h14 : (a - 2) ^ 2 + (a - 2) * (b - 1) + (b - 1) ^ 2 + 3 > 0 := by
          nlinarith [sq_nonneg (a - 2 - (b - 1)), sq_nonneg (a - 2 + (b - 1)), sq_nonneg (a - 2), sq_nonneg (b - 1)]
        linarith
    linarith
  have h15 : a - b = 1 := by linarith
  rw [h15]
  norm_num