import Mathlib

theorem algebra_211727 {x : ℝ} (hx : x ≠ 4) (h : 2 * Real.sqrt (x ^ 2 - 16) + Real.sqrt (x ^ 2 - 9) = 10 / (x - 4)) :
    x = 5 := by
  have h1 : x - 4 ≠ 0 := by
    intro h2
    apply hx
    linarith
  -- field_simp and positivity to equation
  have eq1 : (2 * Real.sqrt (x ^ 2 - 16) + Real.sqrt (x ^ 2 - 9)) * (x - 4) = 10 := by
    have h2 : x - 4 ≠ 0 := h1
    field_simp [h2] at h ⊢
    <;> nlinarith [h, Real.sqrt_nonneg (x ^ 2 - 16), Real.sqrt_nonneg (x ^ 2 - 9)]
  -- discuss x > 4
  by_cases h2 : x > 4
  · -- Assume x > 4, then x - 4 > 0, so the right-hand side is defined. Let's solve for x.
    have h31 : x - 4 > 0 := by linarith
    have h4 : Real.sqrt (x ^ 2 - 16) ≥ 0 := by positivity
    have h44 : Real.sqrt (x ^ 2 - 9) ≥ 0 := by positivity
    nlinarith [sq_nonneg (Real.sqrt (x ^ 2 - 16) - 3), sq_nonneg (Real.sqrt (x ^ 2 - 9) - 4), 
      Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 - 16 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 - 9 by nlinarith), 
      eq1, Real.sqrt_nonneg (x ^ 2 - 16), Real.sqrt_nonneg (x ^ 2 - 9), h31]
  · -- Assume x ≤ 4, then x - 4 ≤ 0
    have h3 : x ≤ 4 := by
      by_cases h4 : x < 4
      · linarith
      · -- x must be 4, contradicting hx: x ≠ 4
        have h5 : x = 4 := by
          linarith
        contradiction
    -- x ≤ 4, and x ≠ 4
    have h6 : x ≤ 4 := by linarith
    have h7 : x ^ 2 - 16 ≥ 0 := by nlinarith [Real.sqrt_nonneg (x ^ 2 - 16), Real.sqrt_nonneg (x ^ 2 - 9), eq1, show x ≤ 4 by linarith, show (x - 4) ≠ 0 from h1]
    have h8 : Real.sqrt (x ^ 2 - 16) ≥ 0 := by positivity
    have h9 : Real.sqrt (x ^ 2 - 9) ≥ 0 := by positivity
    nlinarith [sq_nonneg (Real.sqrt (x ^ 2 - 16) - 3), sq_nonneg (Real.sqrt (x ^ 2 - 9) - 4), 
      Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 - 16 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 - 9 by nlinarith), 
      eq1, Real.sqrt_nonneg (x ^ 2 - 16), Real.sqrt_nonneg (x ^ 2 - 9), show x - 4 ≤ 0 by linarith [h3, show x ≤ 4 from h3, h1]]