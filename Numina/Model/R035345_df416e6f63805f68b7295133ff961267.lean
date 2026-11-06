import Mathlib

theorem algebra_327650 {x y : ℝ} (h1 : x * y + x + y = 17) (h2 : x ^ 2 * y + x * y ^ 2 = 66) :
    x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4 = 12499 := by
  have h3 : x * y = 6 := by
    have h4 : (x + y) = 11 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 11), sq_nonneg (x * y - 6), sq_nonneg (x + y - 6)]
    nlinarith
  have h4 : (x + y) = 11 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 11), sq_nonneg (x * y - 6), sq_nonneg (x + y - 6)]
  have h5 : x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4 = 12499 := by
    have h6 : x + y = 11 := h4
    have h7 : x * y = 6 := h3
    have h8 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
      ring
    have h9 : x ^ 2 + y ^ 2 = 109 := by
      rw [h8]
      rw [h6, h7]
      all_goals nlinarith
    have h10 : x ^ 4 + y ^ 4 = ((x ^ 2 + y ^ 2) ) ^ 2 - 2 * (x * y) ^ 2 := by
      ring
    have h11 : x ^ 3 * y + x * y ^ 3 = (x * y) * (x ^ 2 + y ^ 2) := by
      ring
    nlinarith [h10, h11, h6, h7, h8, h9]
  exact h5