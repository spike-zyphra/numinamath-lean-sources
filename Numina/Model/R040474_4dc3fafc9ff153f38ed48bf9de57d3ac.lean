import Mathlib

theorem algebra_197386 {x1 x2 : ℝ} (hx1 : 5 * x1 ^ 3 - 6 = 0) (hx2 : 6 * x2 ^ 3 - 5 = 0) :
    x1 + x2 > 2 := by
  have h1 : x1 > 0 := by
    nlinarith [sq_nonneg (x1), sq_nonneg (x1 ^ 2), sq_nonneg (x1 - 1), sq_nonneg (x2 ^ 2), sq_nonneg (x2), sq_nonneg (x2 - 1), sq_nonneg (x1 * x2 - 1), sq_nonneg (x1 + x2 - 2)]
  have h2 : x2 > 0 := by
    nlinarith [sq_nonneg (x2), sq_nonneg (x2 ^ 2), sq_nonneg (x2 - 1), sq_nonneg (x1 ^ 2), sq_nonneg (x1), sq_nonneg (x1 - 1), sq_nonneg (x1 * x2 - 1), sq_nonneg (x1 + x2 - 2)]
  have h3 : x1 * x2 = 1 := by
    have h4 : x1 ^ 3 = 6 / 5 := by
      nlinarith
    have h5 : x2 ^ 3 = 5 / 6 := by
      nlinarith
    have h6 : (x1 * x2) ^ 3 = 1 := by
      calc
        (x1 * x2) ^ 3 = x1 ^ 3 * x2 ^ 3 := by ring
        _ = (6 / 5) * (5 / 6) := by rw [h4, h5]
        _ = 1 := by norm_num
    have h7 : x1 * x2 = 1 := by
      have h8 : (x1 * x2) ^ 3 - 1 = 0 := by linarith
      have h9 : (x1 * x2 - 1) * ((x1 * x2) ^ 2 + (x1 * x2) + 1) = 0 := by
        ring_nf at h8 ⊢
        nlinarith
      cases' (mul_eq_zero.mp h9) with h10 h11
      · -- Case x1 * x2 - 1 = 0, so x1 * x2 = 1
        linarith
      · -- Case (x1 * x2) ^ 2 + (x1 * x2) + 1 = 0
        nlinarith [sq_nonneg (x1 * x2 + 1 / 2)]
    exact h7
  have h8 : x1 ≠ x2 := by
    by_contra h
    have h9 : x1 = x2 := by linarith
    have h13 : 5 * x1 ^ 3 = 6 := by linarith
    have h14 : 6 * x2 ^ 3 = 5 := by linarith
    have h15 : x1 ^ 3 = 6 / 5 := by
      linarith
    have h16 : x2 ^ 3 = 5 / 6 := by
      linarith
    have h17 : x1 ^ 3 = x2 ^ 3 := by
      rw [h9]
    nlinarith [h17, h15, h16]
  nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 - 1), sq_nonneg (x2 - 1), h1, h2, h3, h8]