import Mathlib

theorem algebra_309291 {x : ℝ} (hx : x > 0) (h : x^10 + x^5 + 1 / x^5 + 1 / x^10 = 15250) :
    x + 1 / x = 3 := by
  have h1 : x^10 + 1 / x^10 + x^5 + 1 / x^5 = 15250 := by linarith
  -- in order to compute the expression, we need additional hypothesis
  have h3 : (x^5 + 1 / x^5) ^ 2 + (x^5 + 1 / x^5) = 15252 := by
    have h4 : x^10 + 1 / x^10 = (x^5 + 1 / x^5) ^ 2 - 2 := by
      field_simp
      ring
    nlinarith [h4, h1]
  have h4 : x^5 + 1 / x^5 = 123 := by
    have h3_eq : (x^5 + 1 / x^5) ^ 2 + (x^5 + 1 / x^5) = 15252 := h3
    have h5 : (x^5 + 1 / x^5) > 0 := by
      have hx10 : x^5 > 0 := by positivity
      have hx2 : 1 / x^5 > 0 := by positivity
      positivity
    have h6 : (x^5 + 1 / x^5) = 123 := by
      nlinarith [sq_nonneg ((x^5 + 1 / x^5) + 1 / 2), sq_nonneg ((x^5 + 1 / x^5) - 123)]
    exact h6
  have h7 : x^5 + 1 / x^5 = 123 := h4
  -- return to the original hypothesis with the result
  have h8 : x^5 + 1 / x^5 = (x + 1 / x) ^ 5 - 5 * (x + 1 / x) ^ 3 + 5 * (x + 1 / x) := by
    field_simp
    ring
  rw [h8] at h7
  -- now solving the polynomial
  have h9 : (x + 1 / x) ^ 5 - 5 * (x + 1 / x) ^ 3 + 5 * (x + 1 / x) - 123 = 0 := by linarith
  have h10 : (x + 1 / x - 3) * ((x + 1 / x) ^ 4 + 3 * (x + 1 / x) ^ 3 + 4 * (x + 1 / x) ^ 2 + 12 * (x + 1 / x) + 41) = 0 := by
    nlinarith [sq_nonneg ((x + 1 / x) ^ 2 - 9), sq_nonneg ((x + 1 / x) ^ 2 - 4), sq_nonneg (x + 1 / x - 3), sq_nonneg (x * x - 1)]
  cases' (mul_eq_zero.mp h10) with h11 h12
  · -- when `x + 1/x - 3 = 0` holds, the desired result is achieved
    have h13 : x + 1 / x = 3 := by
      linarith
    exact h13
  · -- when the quartic factor `(x+1/x)^4 + 3 * (x+1/x)^3 + 4 * (x+1/x)^2 + 12 * (x+1/x) + 41 = 0` holds, contradiction may rise
    -- For the quartic factor, it's always positive. Let's show it.
    have h13 : (x + 1 / x) ^ 4 + 3 * (x + 1 / x) ^ 3 + 4 * (x + 1 / x) ^ 2 + 12 * (x + 1 / x) + 41 > 0 := by
      have h5 : x + 1 / x > 0 := by
        have h6 : x > 0 := hx
        positivity
      positivity
    have h14 : (x + 1 / x) ^ 4 + 3 * (x + 1 / x) ^ 3 + 4 * (x + 1 / x) ^ 2 + 12 * (x + 1 / x) + 41 = 0 := by
      linarith
    -- From $P > 0$ and $P = 0$, a contradiction is obtained
    nlinarith